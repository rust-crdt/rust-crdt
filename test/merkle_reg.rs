use crdts::merkle_reg::MerkleReg;
use crdts::CmRDT;

#[test]
fn addend_resolves_fork() {
    let mut reg = MerkleReg::new();

    reg.apply(reg.write("a", Default::default()));
    reg.apply(reg.write("b", Default::default()));

    let contents = reg.read();
    assert_eq!(
        contents.values().cloned().collect::<Vec<_>>(),
        vec![&"a", &"b"]
    );

    let parents = contents.keys().cloned().collect();
    reg.apply(reg.write("c", parents));

    let contents = reg.read();
    assert_eq!(contents.values().cloned().collect::<Vec<_>>(), vec![&"c"]);
}
