extern crate crdts;

use crdts::*;

fn main() {
    let mut vclock = VClock::new();
    vclock.apply(Dot::new(31231, 2));
    vclock.apply(Dot::new(4829, 9));
    vclock.apply(Dot::new(87132, 32));
    println!("vclock:\t{}", vclock);

    let mut reg = MVReg::<_, _, u64>::new();

    let op1 = reg.write("some val", reg.read().derive_add_ctx(9_742_820));
    let op2 = reg.write("some other val", reg.read().derive_add_ctx(648_572));
    reg.apply(op1);
    reg.apply(op2);

    println!("reg:\t{}", reg);
}
