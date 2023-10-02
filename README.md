This repository hosts automatically generated Lean toolchains for Lean pull requests.

You should not need to use this repository directly. Instead:
* Once your Lean pull request has the `toolchain-available` label,
* Edit the `lean-toolchain` file in the project you would like to test your pull request in to say:
  `leanprover/lean4-pr-releases:pr-release-NNNN`, where `NNNN` is the number of your pull request.