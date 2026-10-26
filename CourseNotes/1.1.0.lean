/-
 _                       _   _                           _
| |    ___  __ _ _ __   | |_| |__  _ __ ___  _   _  __ _| |__
| |   / _ \/ _` | '_ \  | __| '_ \| '__/ _ \| | | |/ _` | '_ \
| |__|  __/ (_| | | | | | |_| | | | | | (_) | |_| | (_| | | | |
|_____\___|\__,_|_| |_|  \__|_| |_|_|  \___/ \__,_|\__, |_| |_|
                                                   |___/
 _____                           _
| ____|_  ____ _ _ __ ___  _ __ | | ___  ___
|  _| \ \/ / _` | '_ ` _ \| '_ \| |/ _ \/ __|
| |___ >  < (_| | | | | | | |_) | |  __/\__ \
|_____/_/\_\__,_|_| |_| |_| .__/|_|\___||___/
                          |_|

From the Basics to AI-Assisted Formalization

Welcome to Lean! Before we jump into the actual course, allow me to
say a few introductory words.

Please be patient. Lean is a language. A
language used to express something you already know, namely,
mathematics. Learning languages is hard and, at the same time, kind of
magical. You get frustrated and cannot keep track of all the rules and
conventions, until you get used to it. Then everything falls into
place and it is a pleasure to use the language. Between frustration
and pleasure there are only hours of deliberate practice, i.e., of
forcing yourself into unfamiliar parts of the new language. Please
don't give up before your brain does its magic!

This course will consist of (hopefully) short theoretical
explanations, a few examples, and a lot of exercises to force you
into deliberate practice. This does not mean that you should do every
single exercise before jumping to the next topic (there are way too
many exercises!), or that you have to
understand absolutely everything on the first read. You probably
won't, because we have to explain too many things for the time we
have. That's fine, because you can always go to the two books on which
this course is based:
    - [TPIL] J. Avigad, L. de Moura, S. Kong, and S. Ullrich,
      "Theorem Proving in Lean 4",
      https://lean-lang.org/theorem_proving_in_lean4/
    - [MIL] J. Avigad and P. Massot, "Mathematics in Lean",
      https://leanprover-community.github.io/mathematics_in_lean/
These are the two standard references for Lean. I will cite the
relevant parts of the books corresponding to each section of the
course. After the course, if you really want to understand Lean, you
should go ahead and read them.

Finally, I have included some additional explanations in
paragraphs marked with an asterisk, like this:
    (*) This is an additional explanation.
Usually these paragraphs will be more technical, and
may include concepts from later parts of the course. So, unless you
really know what you are doing, or are very curious, please skip them
on a first read.

Without further ado, let's jump to Lean! Enjoy!
-/

/- Day 1: Basic type theory and mathematics -/

/- 1.1 Foundations [TPIL, Chapters 1, 2, 3, 4] -/

/-
In this section you will Learn how the type theory behind Lean
works. You will also have the opportunity to produce plenty of Lean
proofs in the realm of propositional logic.

By the way, the text enclosed like this is a "comment", and is ignored
by Lean.
-/

-- This is also a one-line comment.
