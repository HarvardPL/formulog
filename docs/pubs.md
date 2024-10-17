---
title: Publications and Artifacts
layout: page
nav_order: 6
---

# Publications and Artifacts

Check out our academic papers to learn more about the science behind Formulog.

## Formulog Language Design 

Our [OOPSLA'20 paper](https://dl.acm.org/doi/10.1145/3428209) introduces Formulog, motivates its language design, and demonstrates its use through three extensive case studies.

To cite this paper, please use an entry like this one:

```
@article{Bembenek2020Formulog,
  author  = {Aaron Bembenek and Michael Greenberg and Stephen Chong},
  title   = {Formulog: {D}atalog for {SMT}-{B}ased {S}tatic {A}nalysis},
  journal = {Proceedings of the {ACM} on Programming Languages},
  year    = {2020},
  volume  = {4},
  number  = {OOPSLA},
  doi     = {10.1145/3428209},
  pages   = {141:1--141:31}
}
```

The refereed artifact for this paper is [available on Zenodo](https://zenodo.org/records/4039122). 

## Formulog Performance 

Our [OOPSLA'24 paper](https://dl.acm.org/doi/10.1145/3689754) describes speeding up Formulog via 1) compilation to Soufflé and 2) eager evaluation, a novel Datalog evaluation strategy that works well for some SMT-heavy workloads.

To cite this paper, please use an entry like this one:

```
@article{Bembenek2024Making,
  author  = {Aaron Bembenek and Michael Greenberg and Stephen Chong},
  title   = {Making {F}ormulog {F}ast: An {A}rgument for {U}nconventional {D}atalog {E}valuation},
  journal = {Proceedings of the {ACM} on Programming Languages},
  year    = {2024},
  volume  = {4},
  number  = {OOPSLA2},
  doi     = {10.1145/3689754},
  pages   = {314:1--314:30}
}
```

The refereed artifact for this paper won a [distinguished artifact](https://2024.splashcon.org/track/splash-2024-oopsla-artifacts#distinguished-artifacts) award; it is [available on Zenodo](https://zenodo.org/records/13372573).

## Short Papers

For more information on how Formulog interfaces with external SMT solvers, see the ICLP'20 extended abstract [Datalog-Based Systems Can Use Incremental SMT Solving](https://arxiv.org/html/2009.09158v1/#EPTCS325.7) by Aaron Bembenek, Michael Ballantyne, Michael Greenberg, and Nada Amin ([PDF available here](https://aaronbembenek.github.io/papers/datalog-incr-smt-iclp2020.pdf)).

For an introduction to Formulog geared towards an audience already well versed in Datalog, see the Datalog 2.0'22 short paper [Formulog: Datalog + SMT + FP](https://ceur-ws.org/Vol-3203/short2.pdf) by Aaron Bembenek, Michael Greenberg, and Stephen Chong.