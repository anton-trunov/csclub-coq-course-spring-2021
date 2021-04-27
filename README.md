# Introduction to Formal Verification course at [CS Club](https://compsciclub.ru/)

## Building HTML files locally

- Setup Alectryon using its [installation instructions](https://github.com/cpitclaudel/alectryon/#setup) and add it to your `PATH`.
- Run `make` or `make doc` in the project root directory.

## Lectures

### Lecture 1

- [Intro to formal verification](https://anton-trunov.github.io/csclub-coq-course-spring-2021/slides/intro.html) slides
- Intro to functional programming in Coq: [source](lectures/lecture01.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture01.html)

### Lecture 2

- Polymorphic functions & Dependent functions, Implicit Arguments, Notations, Product types and sum types: [source](lectures/lecture02.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture02.html)

### Lecture 3

- Defining logic, equality. Dependent pattern matching: [source](lectures/lecture03.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture03.html)

### Lecture 4

- Injectivity and disjointness of constructors, large elimination. Convoy pattern. Proofs by induction. `Prop` vs `Type`: [source](lectures/lecture04.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture04.html)

### Lecture 5

- SSReflect tactic language [source](lectures/lecture05.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture05.html)


### Lecture 6

- Proofs by induction: [source](lectures/lecture06.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture06.html)
- [SSReflect proof methodology](https://anton-trunov.github.io/csclub-coq-course-spring-2021/slides/ssreflect-intro-slides.html) slides

### Lecture 7

- Views. `reflect`-predicate. Multi-rewrite rules: [source](lectures/lecture07.v), [rendered](https://anton-trunov.github.io/csclub-coq-course-spring-2021/lectures/lecture07.html)

## Order of lectures, seminars, and homeworks

If you want to go through the course without watching videos of the lectures, you can do that
using the following order of materials:

* [lecture01.v](lectures/lecture01.v)
* [hw01.v](homework/hw01.v)
* [lecture02.v](lectures/lecture02.v)
* [seminar01.v](seminars/seminar01.v)
* [hw02.v](homework/hw02.v)
* [lecture03.v](lectures/lecture03.v)
* [seminar02.v](seminars/seminar02.v) up to and excluding `compA`
* [hw03.v](homework/hw03.v)
* [lecture04.v](lectures/lecture04.v)
* [seminar03.v](seminars/seminar03.v)
* [hw04.v](homework/hw03.v)

and so on, the indices of seminar files lagging one behind the indices of the corresponding lectures.

## Awesome exercise solutions by class participants

- `unit_neq_bool` [solution and generalization](https://gist.github.com/kana-sama/11acc3e66d72f5203faddf403fbbaa4d) by @kana-sama
