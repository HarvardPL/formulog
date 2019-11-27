# Changelog
All notable changes to this project will be documented in this file.

## [Unreleased]
### Fixed
- Require variables in the "names" (i.e., the arguments) of solver variables
  to be bound.

## [0.2.0] - 2019-11-25
### Added
- Support wild card term `??` when "invoking" predicates as functions.
- Constant array constructor `array_const` (from Z3's theory of arrays).
- Ability to do partial magic set rewriting with annotations `@bottomup` and
  `@topdown`.
- Demand transformation simplification for magic set rewriting (following Tekle
  and Liu [2010]).
- Support for record types. 
- Support external input facts via annotation `@external`.
- Support sequential runtime (for debugging) via `sequential` system property.
- Support existential anonymous variables in negated atoms.

### Changed
- Increased the amount of information printed with the `debugMst` option.
- Allow ML-style expressions to occur as logic programming terms.
- Prefix names of automatically-generated ADT testers and getters with `#`.
- Removed syntax highlighting for solver variables.
- Don't require periods after declarations and function definitions.
- Print thread name during SMT debugging.
- Make sure that the same SMT call is never made twice (with the same timeout).

### Fixed
- Fixed bug with applying type substitutions that contain mappings to (possibly
  nested) type variables.
- Updated name of formula type in Vim syntax file.
- Fixed a couple bugs in SMT-LIB parser.
- Fixed bug with missing case in unification algorithm.
- Boolean operators now short circuit.
- Reject programs that use top-down rewriting in combination with IDB
  predicates in the ML fragment.
- Make sure that EDB relations are maintained during top-down rewriting, even
  when they are only referenced in the ML fragment.

## [0.1.0] - 2019-04-21
### Added
- Everything (initial release).
