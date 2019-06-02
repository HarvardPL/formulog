# Changelog
All notable changes to this project will be documented in this file.

## [Unreleased]
### Added
- Constant array constructor `array_const` (from Z3's theory of arrays).
- The option `callTrace`.
- Ability to do partial magic set rewriting with annotations `@bottomup` and
  `@topdown`.
- Demand transformation simplification for magic set rewriting (following Tekle
  and Liu [2010]).
- Support for record types. 

### Changed
- Increased the amount of information printed with the `debugMst` option.
- Allow ML-style expressions to occur as logic programming terms.
- Prefix names of automatically-generated ADT testers and getters with `#`.
- Removed syntax highlighting for solver variables.

### Fixed
- Fixed bug with applying type substitutions that contain mappings to (possibly
  nested) type variables.
- Updated name of formula type in Vim syntax file.
- Fixed a couple bugs in SMT-LIB parser.

## [0.1.0] - 2019-04-21
### Added
- Everything (initial release).
