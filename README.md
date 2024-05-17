# zk-sat

A toy SAT solver that runs on the Nexus zkVM.

## Instructions

Install the Nexus zkVM: https://github.com/nexus-xyz/nexus-zkvm.

```sh
# Run (note that most tests are commented out so proving runs in a reasonable time)
cargo nexus run

# Prove
cargo nexus prove -k32 --impl=par --profile=release

# Verify
cargo nexus verify -k32 --impl=par
```
