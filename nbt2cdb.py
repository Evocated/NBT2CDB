import os
import json
import zlib
import struct
import logging
import traceback
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox
import nbtlib

# --- Logging ---
LOG_PATH = Path(__file__).with_name("cdb_inserter.log")
logging.basicConfig(
    level=logging.DEBUG,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler(LOG_PATH, mode='w', encoding='utf-8')
    ]
)
logger = logging.getLogger(__name__)

# --- Constants ---
MAGIC_CDB = 0xABCDEF99

# --- Globals ---
block_map = {}
inverse_block_map = {}

# --- Utilities ---
def format_block_name(name, props):
    if props:
        return f"{name}[{','.join(f'{k}={v}' for k, v in sorted(props.items()))}]"
    return name

def get_block_id(name):
    return inverse_block_map.get(name, (0, 0))

def encode_position(x: int, z: int, dim: int) -> int:
    if x < 0:
        x += 1 << 14
    if z < 0:
        z += 1 << 14
    x &= 0x3FFF
    z &= 0x3FFF
    dim &= 0xF
    return (dim << 28) | (z << 14) | x

class CDBPosition:
    def __init__(self, val: int):
        self.x = val & 0x3FFF
        self.z = (val >> 14) & 0x3FFF
        self.dimension = (val >> 28) & 0xF

    def to_signed(self):
        signed_size = 1 << 13
        unsigned_size = 1 << 14
        if self.x >= signed_size:
            self.x -= unsigned_size
        if self.z >= signed_size:
            self.z -= unsigned_size

    def parse_position(self):
        self.to_signed()
        return (self.x, self.z, self.dimension)

# --- File Handlers ---
def read_file_header(f):
    hdr_fmt = "<HHIIII"
    size = struct.calcsize(hdr_fmt)
    data = f.read(size)
    if len(data) != size:
        raise ValueError("Bad FileHeader")
    return struct.unpack(hdr_fmt, data)

def read_first_chunk_position(cdb_path: str) -> tuple[int, int, int]:
    with open(cdb_path, "rb") as f:
        f.seek(24)
        _ = f.read(4)
        position_val = struct.unpack("<I", f.read(4))[0]
        pos = CDBPosition(position_val)
        return pos.parse_position()

# --- Index Entry ---
class CDBEntry:
    def __init__(self, x_bitfield, z_bitfield, slot_number, subfile,
                 constant0=0x20FF, unknown0=0xA, unknown1=0x1, constant1=0x8000):
        self.x_bitfield = x_bitfield
        self.z_bitfield = z_bitfield
        self.slot_number = slot_number
        self.subfile = subfile
        self.constant0 = constant0
        self.unknown0 = unknown0
        self.unknown1 = unknown1
        self.constant1 = constant1

    def pack(self):
        return struct.pack(
            "<HHHHHHHH", 
            self.x_bitfield,
            self.z_bitfield,
            self.slot_number,
            self.subfile,
            self.constant0,
            self.unknown0,
            self.unknown1,
            self.constant1
        )

# --- Update Single Index Entry ---
def update_index_entry(cdb_path, x, z, slot_number):
    index_path = Path(cdb_path).with_name("index.cdb")
    if not index_path.exists():
        logger.warning("Index file not found, skipping.")
        return

    x_bf = x & 0x3FFF
    z_bf = z & 0x3FFF
    if x < 0:
        x_bf = (x + (1 << 14)) & 0x3FFF
    if z < 0:
        z_bf = (z + (1 << 14)) & 0x3FFF

    entry = CDBEntry(x_bf, z_bf, slot_number, 0)
    with open(index_path, "ab") as f:
        f.write(entry.pack())
    logger.info(f"Updated index for chunk ({x}, {z}) with slot {slot_number}")

# --- Chunk Writer ---
def write_chunk_to_subfile(f, offset, chunk_x, chunk_z, flat, size):
    width, height, length = size
    raw = bytearray()

    subchunk_count = (height + 15) // 16
    raw.extend(struct.pack("<H", subchunk_count))

    for subchunk in range(subchunk_count):
        # Byte-plane
        for x in range(16):
            for z in range(16):
                for sub_y in range(16):
                    actual_y = subchunk * 16 + sub_y
                    if actual_y >= height:
                        raw.append(0)
                    else:
                        wx = chunk_x * 16 + x
                        wz = chunk_z * 16 + z
                        idx = actual_y * (width * length) + wz * width + wx
                        raw.append(flat[idx][0] if 0 <= idx < len(flat) else 0)

        # Nibble-plane
        nibbles = bytearray(0x1000)
        for sub_y in range(16):
            for z in range(16):
                for x in range(16):
                    actual_y = subchunk * 16 + sub_y
                    if actual_y >= height:
                        nibble_value = 0
                    else:
                        wx = chunk_x * 16 + x
                        wz = chunk_z * 16 + z
                        idx = actual_y * (width * length) + wz * width + wx
                        nibble_value = flat[idx][1] if 0 <= idx < len(flat) else 0

                    local_index = sub_y * 256 + z * 16 + x
                    byte_i = local_index >> 1
                    if (local_index & 1) == 0:
                        nibbles[byte_i] = (nibbles[byte_i] & 0xF0) | nibble_value
                    else:
                        nibbles[byte_i] = (nibbles[byte_i] & 0x0F) | (nibble_value << 4)
        raw.extend(nibbles)

        # Unknown block data
        raw.extend(b'\x00' * 0x800)

    # Footer & Biomes
    raw.extend(b'\x00' * 0x100)
    biomes = bytearray(256)
    for x in range(16):
        for z in range(16):
            wx = chunk_x * 16 + x
            wz = chunk_z * 16 + z
            idx = wz * width + wx
            biomes[x * 16 + z] = flat[idx][0] if 0 <= idx < len(flat) else 1
    raw.extend(biomes)

    comp = zlib.compress(bytes(raw))

    hdr = bytearray()
    hdr += struct.pack("<I", encode_position(chunk_x, chunk_z, 0))
    hdr += struct.pack("<bb", 1, 0)
    hdr += struct.pack("<HHH", 0, 0, 0)

    section_offset = 4 + len(hdr) + (6 * 16)
    hdr += struct.pack("<iiii", 0, section_offset, len(comp), len(raw))
    for _ in range(5):
        hdr += struct.pack("<iiii", -1, 0, 0, 0)

    f.seek(offset)
    f.write(struct.pack("<I", MAGIC_CDB))
    f.write(hdr)
    f.write(comp)

# --- Parse NBT Structure ---
def parse_nbt_structure(nbt_path):
    try:
        nbt_file = nbtlib.load(nbt_path)
        blocks = nbt_file.get("blocks", [])
        size = [int(d) for d in nbt_file.get("size", [0, 0, 0])]
        palette = nbt_file.get("palette", [])
    except Exception as e:
        logger.error(f"Failed NBT parse: {e}\n{traceback.format_exc()}")
        raise ValueError("Invalid NBT")

    palmap = {}
    for i, entry in enumerate(palette):
        name = str(entry.get("Name", "minecraft:air"))
        props = entry.get("Properties", {})
        palmap[i] = format_block_name(name, props)

    width, height, length = size
    total = width * height * length
    flat = [(0, 0)] * total

    for b in blocks:
        x, y, z = int(b["pos"][0]), int(b["pos"][1]), int(b["pos"][2])
        state = int(b.get("state", 0))
        name = palmap.get(state, "minecraft:air")
        rid, meta = get_block_id(name)
        idx = y * (width * length) + z * width + x
        flat[idx] = (rid, meta)

    if len(flat) != total:
        logger.error(f"Flat size {len(flat)} != expected {total}")
        raise ValueError("Size mismatch")

    return flat, size

# --- GUI ---
def browse_json():
    p = filedialog.askopenfilename(filetypes=[("JSON", "*.json")])
    if not p:
        return
    try:
        data = json.load(open(p))
        block_map.clear()
        inverse_block_map.clear()
        for k, v in data.get("blocks", {}).items():
            block_map[k] = v
            inverse_block_map[format_block_name(v, {})] = tuple(map(int, k.split(":")))
        messagebox.showinfo("OK", "Loaded block map")
    except Exception:
        messagebox.showerror("Error", "Failed loading JSON")


def insert_structure(cdb_path, flat, size, start_x, start_z, slot_number):
    index_path = Path(cdb_path).with_name("index.cdb")
    with open(cdb_path, "r+b") as f:
        s0, s1, count, footer, subsize, unk0 = read_file_header(f)
        chunks_x = (size[0] + 15) // 16
        chunks_z = (size[2] + 15) // 16

        for cz in range(chunks_z):
            for cx in range(chunks_x):
                # Process each block individually
                block_count = size[0] * size[1] * size[2] if False else size[1] * 16 * 16
                for block_idx in range(size[1] * 16 * 16):
                    # Could log or handle per-block operations here
                    pass

                # Once the full chunk is "formed", write chunk and update index
                offset = 20 + (cz * chunks_x + cx) * subsize
                write_chunk_to_subfile(f, offset, start_x + cx, start_z + cz, flat, size)
                update_index_entry(cdb_path, start_x + cx, start_z + cz, slot_number)
                slot_number += 1

    logger.info("Structure insertion complete.")


def run_gui():
    root = tk.Tk()
    root.title("NBT→CDB Inserter")

    cdb_var = tk.StringVar()
    nbt_var = tk.StringVar()
    json_var = tk.StringVar()
    x_var = tk.StringVar()
    z_var = tk.StringVar()
    dim_var = tk.StringVar()
    slot_var = tk.StringVar()

    tk.Label(root, text="CDB:").grid(row=0, column=0)
    tk.Entry(root, textvariable=cdb_var, width=50).grid(row=0, column=1)
    tk.Button(root, text="…", command=lambda: (
        cdb_var.set(filedialog.askopenfilename(filetypes=[("CDB", "*.cdb")])),
        browse_json(),
        x_var.set(str(read_first_chunk_position(cdb_var.get())[0])),
        z_var.set(str(read_first_chunk_position(cdb_var.get())[1])),
        dim_var.set(str(read_first_chunk_position(cdb_var.get())[2]))
    )).grid(row=0, column=2)

    tk.Label(root, text="NBT:").grid(row=1, column=0)
    tk.Entry(root, textvariable=nbt_var, width=50).grid(row=1, column=1)
    tk.Button(root, text="…", command=lambda: nbt_var.set(filedialog.askopenfilename(filetypes=[("NBT", "*.nbt")]))).grid(row=1, column=2)

    tk.Label(root, text="blocks.json:").grid(row=2, column=0)
    tk.Entry(root, textvariable=json_var, width=50).grid(row=2, column=1)
    tk.Button(root, text="…", command=lambda: [
        json_var.set(filedialog.askopenfilename(filetypes=[("JSON", "*.json")])),
        browse_json()
    ]).grid(row=2, column=2)

    tk.Label(root, text="Start chunk X:").grid(row=3, column=0)
    tk.Entry(root, textvariable=x_var).grid(row=3, column=1)
    tk.Label(root, text="Start chunk Z:").grid(row=4, column=0)
    tk.Entry(root, textvariable=z_var).grid(row=4, column=1)
    tk.Label(root, text="Dimension:").grid(row=5, column=0)
    tk.Entry(root, textvariable=dim_var).grid(row=5, column=1)
    tk.Label(root, text="Slot Number:").grid(row=6, column=0)
    tk.Entry(root, textvariable=slot_var).grid(row=6, column=1)

    def on_insert():
        try:
            flat, size = parse_nbt_structure(nbt_var.get())
            slot_number = int(slot_var.get())
            insert_structure(cdb_var.get(), flat, size, int(x_var.get()), int(z_var.get()), slot_number)
            messagebox.showinfo("Done", "Structure inserted")
        except Exception as e:
            logger.error("Insert error:\n" + traceback.format_exc())
            messagebox.showerror("Error", str(e))

    tk.Button(root, text="Insert", command=on_insert).grid(row=7, column=1)
    root.mainloop()

if __name__ == "__main__":
    run_gui()
