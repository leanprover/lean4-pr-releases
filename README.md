This repository hosts automatically generated Lean [toolchains](https://github.com/leanprover/elan#elan-lean-version-manager) for Lean [pull requests](https://github.com/leanprover/lean4/pulls).

You should not need to use this repository directly. Instead:
* Once your Lean pull request has the [`toolchain-available`](https://github.com/leanprover/lean4/pulls?q=is%3Apr+is%3Aopen+label%3Atoolchain-available) label,
* Edit the `lean-toolchain` file in the project you would like to test your pull request in to say:
  `leanprover/lean4-pr-releases:pr-release-NNNN`, where `NNNN` is the number of your pull request.