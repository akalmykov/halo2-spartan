# Halo2 Spartan

## Build

Because there is no crate for Spartan2 repo, you need to clone it in the same directory

```sh
git clone https://github.com/akalmykov/halo2-spartan.git
git clone git@github.com:microsoft/Spartan2.git
cd halo2-spartan
cargo run --example spartan -- --name spartan -k 8 prove
cargo run --example spartan -- --name spartan -k 8 verify
```
