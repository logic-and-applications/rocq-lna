# Changelog

This LA library is based on two files used for Proofweb called BenB and BenB2, used by the Radboud University Computing Science course 'Logic and Applications'. This first library was maintained on a no longer public BitBucket repo, so a copy of the 2024 version is visible in the [BenB] branch for easier comparison.

## [Unreleased]

## [1.0.0] - 2024-11-13

### Added

- helper tactics for changed `lin_solve`:
  - `is_singleton_eq` which fails terms that are not singleton linear equations
  - `lin_solve_remove_hyps` which removes all hypotheses that are not singleton linear equations
- a helper tactic for `splitAss` (now `curry_assumptions`) called `curry_assumptions_go`
- a test file called `tests.v` which tests tactic implementations

### Changed

- Renamed `splitAss` to `curry_assumptions`.
- Made all Ltac tactics use Tactic Notation if possible (no use of recursion)
- definition of lin_solve to no longer use deprecated fourier.
  - to match desired behaviour, only hypotheses that are singleton linear expressions are used and similarly the goal must be a singleton linear expression
- definition of curry_assumptions, stru_ihould work for any depth now
- `interval` tactic fails with appropriate error message on non-interval goals
- Some following tactics no make use of now removed unused tacticsi no

### Deprecated

### Removed

- removed the following unused tactics:
  - tru_i
  - eqv_i
  - eqv_e1
  - eqv_e2
  - negneg_i
  - negneg_e
  - PCB
  - RAA
  - MT
  - equ_i
  - equ_e
  - equ_e'
- removed module 'old' containing
  - unused imp_i
  - unused all_i
- removed section labeled as 'old tactics' containing unused
  - dis_els
  - dn_axiom
  - neg_ins
  - neg_els
  - exi_els
- removed seemingly unused Notation B := Prop.
- removed strange changes in notation for expressions like `x <= y /\ v <= z`
- removed seemingly unused (in)equality solving tactics:
  - prove_inequality
  - prove_equality
- removed nested exists notation, as it is already part of standard library for any number
- removed commented-out section labeled 'unchanged names' containing
  - con_e1
  - con_e2
  - dis_i1
  - dis_i2
  - dis_e
  - imp_i
  - imp_e
  - neg_e
  - all_i
  - exi_i
  - exi_e
- removed commented-out section labeled 'unused tactics' containing
  - eqv_in
  - eqv_ell
  - eqv_elr
  - negneg_in
  - equ_in
  - equ_el
  - equ_els
- removed commented-out notation for set intervals

## [0.0.1] - 2024 (BenB)

- Original 2024 version of the BenB library

<!-- Versions -->

[unreleased]: https://github.com/Author/Repository/compare/v0.1.0...HEAD
[1.0.0]: https://github.com/cas-haaijman/LA/compare/BenB...v1.0.0
[0.0.1]: https://github.com/cas-haaijman/LA/releases/tag/BenB
