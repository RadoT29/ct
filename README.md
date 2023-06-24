# Category Theory Library in Lean 3

## Description
This is a computer-checked library of definitions, theorems, proofs and examples in the field of category theory in Lean 3.

## Installation
To run this project, you must install the following tools:
- [LEAN 3](https://leanprover-community.github.io/get_started.html)
- [`leanproject`](https://leanprover-community.github.io/leanproject.html)

When you have those installed, you can clone the repository and build the project with the following:
```bash
git clone git@gitlab.ewi.tudelft.nl:bpahrens/ct.git
cd ct
leanproject build
```
You should see it build without any problems.

## Gitlab CI/CD

 Currently there is no docker image for LEAN 4.
 This means we cannot easily set up the Gitlab Pipeline for it.
 But, there is an image for LEAN 3, therefore, we have decided to use the older version.
 
 The pipeline simply runs the command `leanproject build` on the project.
 This command will only return ok, if all code in the library is error free, ergo it is sound.

## Authors and acknowledgment

- Students:
  - Ciprian Stanciu
  - Csanád Farkas
  - Markus Orav
  - Pedro Brandão Brandao de Araujo
  - Rado Todorov
- Supervisors:
  - Benedikt Ahrens
  - Lucas Escot

## Project status
The project was developed as a Research Project for a university course of the same name, given by TU Delft.
There are currently no plans beyond this course.

## License
Copyright (C) 2023 by Ciprian Stanciu, Csanád Farkas, Markus Orav, Pedro Brandão Brandao de Araujo, Rado Todorov 

Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted.