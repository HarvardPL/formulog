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

### Changed
- Increased the amount of information printed with the `debugMst` option.

### Fixed
- Fix bug with applying type substitutions that contain mappings to (possibly
  nested) type variables.
- Updated name of formula type in Vim syntax file.

## [0.1.0] - 2019-04-21
### Added
- Everything (initial release).
