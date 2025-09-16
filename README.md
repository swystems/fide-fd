# TLA+ specs for FiDe algorithms

TLA+ specifications for Hierarchical Stabilizing Uniform Consensus (HSUC) and
Heartbeat Uniform Consensus (HUC) protocols from FiDe's ATC25 paper: 
[FiDe: Reliable and Fast Crash Failure Detection to Boost Datacenter Coordination](https://www.usenix.org/conference/atc25/presentation/rovelli)

## Verify with TLC

Download the `tla2tools.jar` from [TLA+ releases](https://github.com/tlaplus/tlaplus/releases)

Edit config in respective `.cfg` file and run TLC:

```sh
java -jar tla2tools.jar HUC.tla   #HUC
java -jar tla2tools.jar HSUC.tla   #HSUC
```