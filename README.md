#AAAAA rust-crdt
[![Build Status](https://travis-ci.org/spacejam/rust-crdt.svg?branch=master)](https://travis-ci.org/spacejam/rust-crdt)
[![crates.io](http://meritbadge.herokuapp.com/crdts)](https://crates.io/crates/crdts)

Thoroughly tested serializable practical CRDT's ported from riak_dt.


[documentation](http://spacejam.github.io/docs/crdts/crdts/)


If you want to learn about how CRDTs work, I suggest starting with the readme from [aphyr's meangirls](https://github.com/aphyr/meangirls) repo.
Afterwards, either check out the [riak dt](https://github.com/basho/riak_dt) source code or [A comprehensive study of CRDTs](https://hal.inria.fr/file/index/docid/555588/filename/techreport.pdf) depending on if you like to read papers or jump straight to source code examples.


- [x] Vector Clock
- [x] ORSWOT
- [x] LWW Register
- [x] G-Counter
- [ ] Map
- [ ] G-Set
- [ ] OR-Set
- [ ] PN-Counter
- [ ] EM-Counter

# references

- [A comprehensive study of CRDTs](https://hal.inria.fr/file/index/docid/555588/filename/techreport.pdf)

- [riak dt - Convergent replicated datatypes in Erlang](https://github.com/basho/riak_dt)
