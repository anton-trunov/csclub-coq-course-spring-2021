# Introduction to Formal Verification course at [CS Club](https://compsciclub.ru/)

## Building HTML files locally

- Setup Alectryon using its [installation instructions](https://github.com/cpitclaudel/alectryon/#setup) and add it to your `PATH`. (You need Alectryon at commit df5664e71c1026af4aaf69e6b227d427a728e7c6 or newer).
- Run `make` or `make doc` in the project root directory.

## Classes

### Class 1

- [Intro to formal verification](https://anton-trunov.github.io/csclub-coq-course-spring-2021/slides/intro.html) slides
- Intro to functional programming in Coq: [source](lectures/lecture01.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture01.html)
- No seminar
- Homework: [hw01.v](homework/hw01.v)

### Class 2

- Polymorphic functions & Dependent functions, Implicit Arguments, Notations, Product types and sum types: [source](lectures/lecture02.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture02.html)
- Seminar: [seminar01.v](seminars/seminar01.v)
- Homework: [hw02.v](homework/hw02.v)

### Class 3

- Defining logic, equality. Dependent pattern matching: [source](lectures/lecture03.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture03.html)
- Seminar: [seminar02.v](seminars/seminar02.v)
- Homework: [hw03.v](homework/hw03.v)

### Class 4

- Injectivity and disjointness of constructors, large elimination. Convoy pattern. Proofs by induction. `Prop` vs `Type`: [source](lectures/lecture04.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture04.html)
- Seminar: [seminar03.v](seminars/seminar03.v)
- Homework: [hw04.v](homework/hw04.v)

### Class 5

- SSReflect tactic language [source](lectures/lecture05.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture05.html)
- Seminar: [seminar04.v](seminars/seminar04.v)
- Homework: [hw05.v](homework/hw05.v)


### Class 6

- Proofs by induction: [source](lectures/lecture06.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture06.html)
- [SSReflect proof methodology](https://anton-trunov.github.io/csclub-coq-course-spring-2021/slides/ssreflect-intro-slides.html) slides
- Seminar: [seminar05.v](seminars/seminar05.v)
- Homework: [hw06.v](homework/hw06.v)

### Class 7

- Views. `reflect`-predicate. Multi-rewrite rules: [source](lectures/lecture07.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture07.html)
- Seminar: [seminar06.v](seminars/seminar06.v)
- Homework: [hw07.v](homework/hw07.v)

### Class 8

- [Canonical Structures & Hierachies](https://anton-trunov.github.io/csclub-coq-course-spring-2021/slides/slides/lecture08.html) slides
- Canonical Structures & Hierachies: [demo (source)](lectures/lecture08_demo.v), [demo (rendered)](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture08_demo.html)
- Seminar: [seminar07.v](seminars/seminar07.v)
- Homework: [hw08.v](homework/hw08.v)

### Class 9

- Verification of insertion sort and merge sort. Non-structurally recursive functions. Nested `fix` pattern. `Program` plugin. `Acc`-predicate. [source](lectures/lecture09.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture09.html)
- Seminar: [seminar08.v](seminars/seminar08.v)
- Homework: [hw09.v](homework/hw09.v)

### Class 10

- A potpourri of tools: automation (linear integer arithmetic, hammers), Equations plugin, property based randomized testing, mutation proving, extraction [source](lectures/lecture10.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture10.html)
- Seminar: [seminar09.v](seminars/seminar09.v)
- Homework: no homework

## Awesome exercise solutions by class participants

- `unit_neq_bool` [solution and generalization](https://gist.github.com/kana-sama/11acc3e66d72f5203faddf403fbbaa4d) by @kana-sama
- A compiler from a language of arithmetic expressions to a stack language: [solution and generalization](https://gist.github.com/kana-sama/dfda1465dae66e65a3fe9e466462bf18) by @kana-sama
