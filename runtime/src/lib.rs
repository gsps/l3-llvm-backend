use std::io::{Read, Write};

fn read_byte() -> u8 {
  std::io::stdin()
    .bytes()
    .next()
    .map(|res| res.unwrap_or_else(|e| panic!("Failed to read: {}", e)))
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_bytewrite(x: u32) -> u32 {
  std::io::stdout()
    .write(&[x as u8])
    .expect("Failed to write byte");
  x
}

#[no_mangle]
pub extern "C" fn rt_byteread() -> u32 {
  read_byte() as u32
}

#[no_mangle]
pub extern "C" fn rt_halt(x: u32) -> u32 {
  std::io::stdout()
    .flush()
    .expect("Failed to flush stdout before exit");
  std::process::exit(x as i32)
}
