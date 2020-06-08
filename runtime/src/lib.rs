fn read_byte() -> u8 {
  use std::io::Read;
  std::io::stdin().bytes().next().unwrap().ok().unwrap()
}

#[no_mangle]
pub extern "C" fn rt_bytewrite(x: u32) -> u32 {
  read_byte();
  x
}

#[no_mangle]
pub extern "C" fn rt_byteread() -> u32 {
  read_byte() as u32
}

#[no_mangle]
pub extern "C" fn rt_halt(x: u32) -> u32 {
  println!("(EXIT! {})", x);
  std::process::exit(x as i32)
}
