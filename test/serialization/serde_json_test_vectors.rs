use std::{
    collections::{BTreeSet, HashSet},
    fs::File,
    io::Write,
    io::{self, BufRead, BufReader},
};

use crdts::{
    merkle_reg::MerkleReg, CmRDT, Dot, GCounter, GList, GSet, LWWReg, List, MVReg, Map, Orswot,
    PNCounter, VClock,
};

const TEST_VECTOR_FILE: &str = "./test/serialization/serde_json_test_vector.jsonl";

fn gen_dot() -> Dot<String> {
    Dot {
        actor: "bob".into(),
        counter: 21,
    }
}

fn gen_gcounter() -> GCounter<String> {
    let mut c = GCounter::new();

    c.apply(c.inc("alice".into()));
    c.apply(c.inc("bob".into()));
    c.apply(c.inc("alice".into()));
    c.apply(c.inc("caleb".into()));
    c.apply(c.inc("caleb".into()));
    c.apply(c.inc("caleb".into()));
    c.apply(c.inc("dan".into()));

    c
}

fn gen_glist() -> GList<char> {
    let mut l = GList::new();

    l.apply(l.insert(0, 'l'));
    l.apply(l.insert(0, 'e'));
    l.apply(l.insert(2, 'l'));
    l.apply(l.insert(0, 'h'));
    l.apply(l.insert(4, 'o'));

    assert_eq!(l.read::<String>(), "hello");
    l
}

fn gen_gset() -> GSet<char> {
    let mut l = GSet::new();

    l.insert('l');
    l.insert('e');
    l.insert('l');
    l.insert('h');
    l.insert('o');

    assert_eq!(l.read(), BTreeSet::from_iter("helo".chars()));
    l
}

fn gen_list() -> List<char, String> {
    let mut l = List::new();

    l.apply(l.insert_index(0, 'l', "alice".into()));
    l.apply(l.insert_index(0, 'e', "bob".into()));
    l.apply(l.insert_index(2, 'l', "caleb".into()));
    l.apply(l.insert_index(0, 'h', "caleb".into()));
    l.apply(l.insert_index(4, 'o', "dan".into()));

    assert_eq!(l.read::<String>(), "hello");
    l
}

fn gen_lwwreg() -> LWWReg<String, u64> {
    let mut reg = LWWReg::new("first".into(), 0);
    reg.update("second".into(), 1);
    reg.update("late".into(), 0);

    reg
}

fn gen_map() -> Map<String, MVReg<u64, String>, String> {
    let mut m: Map<String, MVReg<u64, String>, String> = Map::new();

    let add_ctx_bob = m.read_ctx().derive_add_ctx("bob".into());
    let add_ctx_alice = m.read_ctx().derive_add_ctx("alice".into());
    m.apply(m.update("age", add_ctx_bob, |reg, a| reg.write(34, a)));

    let add_ctx_bob = m.read_ctx().derive_add_ctx("bob".into());
    m.apply(m.update("height", add_ctx_bob, |reg, a| reg.write(152, a)));

    m.apply(m.update("height", add_ctx_alice, |reg, a| reg.write(156, a)));

    assert_eq!(m.get(&"age".into()).val.unwrap().read().val, vec![34]);
    assert_eq!(
        m.get(&"height".into()).val.unwrap().read().val,
        vec![152, 156]
    );
    m
}

fn gen_merkle_reg() -> MerkleReg<String> {
    let mut reg = MerkleReg::new();

    let n1 = reg.write("first".into(), BTreeSet::new());
    let n1_hash = n1.hash();
    reg.apply(n1);
    let n2 = reg.write("second".into(), BTreeSet::new());
    let n2_hash = n2.hash();
    reg.apply(n2);
    reg.apply(reg.write("last".into(), BTreeSet::from([n1_hash, n2_hash])));

    assert_eq!(Vec::from_iter(reg.read().values()), vec!["last"]);
    reg
}

fn gen_mvreg() -> MVReg<u64, String> {
    let mut reg: MVReg<u64, String> = MVReg::new();

    let add_ctx_bob = reg.read_ctx().derive_add_ctx("bob".into());
    let add_ctx_alice = reg.read_ctx().derive_add_ctx("alice".into());
    reg.apply(reg.write(12, add_ctx_bob));
    reg.apply(reg.write(21, add_ctx_alice));
    assert_eq!(reg.read().val, vec![12, 21]);
    reg
}

fn gen_orswot() -> Orswot<u64, String> {
    let mut set: Orswot<u64, String> = Orswot::new();

    let add_ctx_bob = set.read_ctx().derive_add_ctx("bob".into());
    let add_ctx_alice = set.read_ctx().derive_add_ctx("alice".into());
    set.apply(set.add(42, add_ctx_bob));
    set.apply(set.add(1, add_ctx_alice));
    assert_eq!(set.read().val, HashSet::from_iter([42, 1]));
    set
}

fn gen_pncounter() -> PNCounter<String> {
    let mut c = PNCounter::new();

    c.apply(c.inc("alice".into()));
    c.apply(c.dec("bob".into()));
    c.apply(c.inc("alice".into()));
    c.apply(c.dec("caleb".into()));
    c.apply(c.dec("caleb".into()));
    c.apply(c.dec("caleb".into()));
    c.apply(c.inc("dan".into()));

    assert_eq!(c.read(), num::BigInt::from(-1));
    c
}

fn gen_vclock() -> VClock<String> {
    let mut c = VClock::new();

    c.apply(c.inc("alice".into()));
    c.apply(c.inc("bob".into()));
    c.apply(c.inc("alice".into()));
    c.apply(c.inc("caleb".into()));
    c.apply(c.inc("caleb".into()));
    c.apply(c.inc("caleb".into()));
    c.apply(c.inc("dan".into()));

    c
}

#[test]
fn test_serde_json_test_vectors() -> Result<(), io::Error> {
    let crdts = [
        serde_json::to_string(&gen_dot())?,
        serde_json::to_string(&gen_gcounter())?,
        serde_json::to_string(&gen_glist())?,
        serde_json::to_string(&gen_gset())?,
        serde_json::to_string(&gen_list())?,
        serde_json::to_string(&gen_lwwreg())?,
        serde_json::to_string(&gen_map())?,
        serde_json::to_string(&gen_merkle_reg())?,
        serde_json::to_string(&gen_mvreg())?,
        serde_json::to_string(&gen_orswot())?,
        serde_json::to_string(&gen_pncounter())?,
        serde_json::to_string(&gen_vclock())?,
    ];

    let f = match File::open(TEST_VECTOR_FILE) {
        Ok(f) => f,
        Err(_) => {
            let mut f = File::create(TEST_VECTOR_FILE)?;
            for crdt in crdts {
                writeln!(f, "{}", crdt)?;
            }
            panic!("Missing test vectors have been written, re-run test");
        }
    };

    let lines = Vec::from_iter(BufReader::new(f).lines());
    assert_eq!(crdts.len(), lines.len());
    for (crdt, line) in crdts.into_iter().zip(lines) {
        assert_eq!(crdt, line?);
    }
    Ok(())
}
