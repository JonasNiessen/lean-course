/- 1.1.1 Formal verification and Lean -/

/-
What is a proof? On paper, a proof is an argument that convinces
other mathematicians (a referee, your advisor, your future self) that
a statement is true. Formal verification goes one step further: the
proof is written in a language so precise that a computer program can
check that every single step follows from the rules of logic and from
previously proven results. There is no room for "it is easy to see".

There are two big families of programs that deal with proofs:
    - Automated theorem provers (ATPs), such as Vampire or E, try to
      find proofs by themselves. They are very good at searching
      through many short arguments, but they get lost very quickly in
      the kind of mathematics we do every day.
    - Interactive theorem provers (ITPs), also called proof
      assistants, such as Isabelle, Rocq (formerly Coq) or Lean. Here
      you write the proof, and the program checks it, tells you what
      is left to prove, and fills in boring details when it can. It is
      a dialogue between you and the computer, hence "interactive".

Lean is an interactive theorem prover and, at the same time, a
functional programming language. Its logical foundation is a
dependent type theory (see 1.1.2), and all the mathematics you write
is ultimately checked by a small program at its core, the kernel.

Leonardo de Moura started Lean at Microsoft Research in 2013. If you
want to know the cool story behind the origins of Lean, I strongly recommend:
    - [PITC] K. Hartnett, "The Proof in the Code: How a Truth Machine
      Is Transforming Math and AI", Quanta Books, 2026.

    (*) Why should you trust Lean? Because of the de Bruijn criterion.
    What you write in Lean (notation, implicit arguments, tactics,
    automation) is not checked directly. First, the elaborator
    translates it into a proof term, a fully explicit term of the
    underlying type theory. The elaborator is big, complicated, and
    may well have bugs. Then, the kernel type-checks this proof term.
    The kernel is small and simple, and it is the only part of Lean
    you have to trust. This is the de Bruijn criterion: a proof
    assistant should produce proof terms that can be checked by a
    small, independent checker. So, if a tactic (or an AI) goes
    wrong, the worst that can happen is that the kernel rejects the
    proof, never that a false theorem is accepted. And if you do not
    trust Lean's kernel either, there are independent
    reimplementations of it that you can use to check the proofs
    again. Lean's own kernel is written in C++, but proofs can be
    exported and checked, for instance, by
        - nanoda, written in Rust by Chris Bailey,
        - lean4lean, written in Lean itself by Mario Carneiro, with
          the long-term goal of proving that the checker is correct,
        - con-leche, written in Lean, which comes with a consistency
          proof: if it accepts some declarations, they have a
          set-theoretic model, so it can never accept a proof of
          False, and
        - con-ron, a port of con-leche to Rust, whose consistency is
          argued by translating its Rust code back into Lean.
    The last two were developed at the Lean FRO and, fittingly for
    this course, they were written by an AI (Claude) under close
    human supervision. The Lean Kernel Arena
    (https://arena.lean-lang.org) collects these checkers and tests
    them against each other on tricky examples. Since Lean v4.35, all
    of them have been shipped with Lean, and
    lake check --paranoid accepts a project only if every one of them
    does. A bug would now have to be present in several different
    implementations, written in different languages, for a false
    proof to go unnoticed.
-/
