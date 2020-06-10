use std::io::{Read, Write};

pub type Value = u32;

#[no_mangle]
pub extern "C" fn rt_halt(x: Value) -> Value {
  std::io::stdout()
    .flush()
    .expect("Failed to flush stdout before exit");
  std::process::exit(x as i32)
}

/// IO

fn read_byte() -> u8 {
  std::io::stdin()
    .bytes()
    .next()
    .map(|res| res.unwrap_or_else(|e| panic!("Failed to read: {}", e)))
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_bytewrite(x: Value) -> Value {
  std::io::stdout()
    .write(&[x as u8])
    .expect("Failed to write byte");
  std::io::stdout()
    .flush()
    .expect("Failed to flush stdout");
  x
}

#[no_mangle]
pub extern "C" fn rt_byteread() -> Value {
  read_byte() as Value
}

/// Simple bump allocator

const MEMORY_SIZE: usize = 1024 * 1024 / 4;

#[used]
#[no_mangle]
pub static mut MEMORY: [Value; MEMORY_SIZE] = [0; MEMORY_SIZE];
static mut MEMORY_OFFSET: usize = 0;

fn pack_header(tag: u8, size: u32) -> Value {
  size << 8 | (tag as Value)
}

fn unpack_header(header: Value) -> (u8, u32) {
  (header as u8, header >> 8)
}

fn block_as_offset(block: Value) -> usize {
  let offset = block as usize;
  assert!(offset > 0 && offset < MEMORY_SIZE);
  offset
}

#[no_mangle]
pub extern "C" fn rt_blockalloc(tag: u32, size: Value) -> Value {
  assert!(tag < 0xff);
  let old_offset = unsafe { MEMORY_OFFSET };
  let new_offset = old_offset + (size as usize) + 1;
  if new_offset as usize > MEMORY_SIZE {
    panic!("Out of memory");
  }
  unsafe {
    MEMORY[old_offset] = pack_header(tag as u8, size);
    MEMORY_OFFSET = new_offset
  };
  (old_offset + 1) as Value
}

#[no_mangle]
pub extern "C" fn rt_blocktag(block: Value) -> Value {
  let (tag, _) = unpack_header(unsafe { MEMORY[block_as_offset(block) - 1] });
  tag as Value
}

#[no_mangle]
pub extern "C" fn rt_blocklength(block: Value) -> Value {
  let (_, size) = unpack_header(unsafe { MEMORY[block_as_offset(block) - 1] });
  size as Value
}

#[no_mangle]
pub extern "C" fn rt_blockget(block: Value, offset: Value) -> Value {
  let block_offset = block_as_offset(block);
  let (_, size) = unpack_header(unsafe { MEMORY[block_offset - 1] });
  assert!(offset < size);
  unsafe { MEMORY[block_offset + (offset as usize)] }
}

#[no_mangle]
pub extern "C" fn rt_blockset(block: Value, offset: Value, value: Value) -> Value {
  let block_offset = block_as_offset(block);
  let (_, size) = unpack_header(unsafe { MEMORY[block_offset - 1] });
  assert!(offset < size);
  unsafe { MEMORY[block_offset + (offset as usize)] = value; }
  0
}
