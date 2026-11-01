/- 1.1.4 Quantifiers, classical logic, and equality -/

section

variable (p q r : Prop)

/-
Propositional logic is not enough to do mathematics: we want to say
"for all x" and "there exists x". Let us fix a type α (typed \a) and
two predicates on it, i.e., functions that take a term of α and
return a proposition:
-/

variable (α : Type) (P Q : α → Prop)

/-
Remember dependent functions from 1.1.2? A proof of ∀ x, P x (typed
\forall) is a function that takes any x : α and returns a proof of
P x. Its type is precisely the dependent function type (x : α) → P x,
since the output type P x depends on the input x. So, again, to prove
a ∀ you write a fun, and to use it you apply it:
-/

example (h : ∀ x, P x) (a : α) : P a := h a

example (h : ∀ x, P x ∧ Q x) : ∀ x, P x := fun x => (h x).1

example : (∀ x, P x → Q x) → (∀ x, P x) → ∀ x, Q x :=
  fun hPQ => (fun hP => (fun x => (hPQ x) (hP x)))

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := sorry

example : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := sorry

/-
A proof of ∃ x, P x (typed \exists) is a pair: a witness w : α
together with a proof of P w. To prove it you use the anonymous
constructor, and to use it you take the pair apart, either with
Exists.elim or directly with ⟨ ⟩ in the fun:
-/

example (a : α) (h : P a) : ∃ x, P x := ⟨a, h⟩

example : ∃ n : Nat, n + n = 6 := ⟨3, rfl⟩

/-
Using an existential is a bit more subtle. On paper, from "there
exists x such that P x" we say "let w be such that P w" and carry on
with the proof. This is exactly what Exists.elim does. Let us look at
its type:
-/

#check Exists.elim
-- Exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
--   (h₁ : ∃ x, p x) (h₂ : ∀ (a : α), p a → b) : b

/-
Read it as follows: if we want to prove some proposition b, and we
know h₁ : ∃ x, p x, it is enough to give h₂, a proof that b follows
from p a for an arbitrary a. Note that b cannot depend on a: we know
that some witness exists, but not which one, so whatever we conclude
must hold for any of them.

The arguments in curly braces {α} {p} {b} are implicit: we do not
write them, because Lean can figure them out from h₁ and from what we
are proving. (Sort u is a generalization of Type that also includes
Prop. You can ignore it for now.) So in practice we only write
Exists.elim h₁ h₂:
-/

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x :=
  Exists.elim h (fun w hw => ⟨w, hw.2⟩)

/-
Here b is ∃ x, Q x, and h₂ is the function fun w hw => ⟨w, hw.2⟩,
which takes a witness w and a proof hw of P w ∧ Q w, and returns a
proof of ∃ x, Q x with the same witness.

How do you keep track of all this? You do not have to: Lean does it
for you. Hover with the mouse over any term in the example above, and
a small window will show you its type:
    - over Exists.elim, you get its type (as above) together with its
      documentation,
    - over w, you get w : α,
    - over hw, you get hw : P w ∧ Q w,
    - over the .2 in hw.2, you get that it is a proof of Q w.
Get used to hovering all the time, especially over terms you do not
recognize. It is the fastest way to understand a piece of Lean code
(and to find out why it does not work). You can even hover over the
symbols, such as ∃ or ⟨ ⟩, to learn what they mean.

Finally, taking a pair apart is so common that we can do it directly
in the fun, with the anonymous constructor:
-/

example : (∃ x, P x ∧ Q x) → ∃ x, Q x := fun ⟨w, hw⟩ => ⟨w, hw.2⟩

example : (∀ x, P x → Q x) → (∃ x, P x) → ∃ x, Q x := sorry

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  ⟨fun hPQ => Exists.elim hPQ (fun a hPQa => Or.elim hPQa (fun hP =>
  Or.inl ⟨a, hP⟩) (fun hQ => Or.inr ⟨a, hQ⟩)),
  fun hPQ => Or.elim hPQ (fun ⟨a, hPa⟩ => ⟨a, Or.inl hPa⟩) (fun ⟨a,
  hQa⟩ => ⟨a, Or.inr hQa⟩)⟩

example : (¬∃ x, P x) ↔ ∀ x, ¬P x := sorry

example : (∃ x, ¬P x) → ¬∀ x, P x := sorry

/-
Now, classical logic. Everything we have done so far is constructive:
to prove p ∨ q we have to say which one holds, and to prove ∃ x, P x
we have to give a witness. As mathematicians we usually allow for
classical (i.e., non-constructive) arguments, and Lean lets us reason classically
through the namespace Classical. The two results you need to know are
the law of excluded middle and proof by contradiction:
-/

#check Classical.em               -- Classical.em (p : Prop) : p ∨ ¬p
#check Classical.byContradiction  -- (h : ¬p → False) : p

example (h : ¬¬p) : p :=
  Or.elim (Classical.em p) (fun hp => hp) (fun hnp => False.elim (h hnp))

example (h : ¬¬p) : p := Classical.byContradiction (fun hnp => h hnp)

example : (¬q → ¬p) → (p → q) :=
  fun hqp => (fun hp => Or.elim (Classical.em q) (fun hq => hq) (fun
  hnq => ( False.elim (hqp hnq hp) ) ))

example : (p → q) → ¬p ∨ q :=
  fun hpq => Or.elim (Classical.em p) (fun hp => Or.inr (hpq hp))
  (fun hnp => Or.inl hnp)

example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry

example : (¬∀ x, P x) → ∃ x, ¬P x := sorry  -- harder

/-
    (*) Lean's logic is constructive, plus three axioms: propext
    (equivalent propositions are equal), Quot.sound (for quotients),
    and Classical.choice. Excluded middle is a theorem, deduced from
    choice (this is Diaconescu's theorem). Use #print axioms on the
    examples above to see which axioms they depend on. Mathlib uses
    classical logic everywhere, so you can forget about this
    distinction unless you are interested in constructive mathematics.

Finally, equality. For any two terms a b : α, a = b is a proposition.
We have already used rfl, which proves a = a. It works whenever both
sides compute to the same thing, which is why ⟨3, rfl⟩ above proves
3 + 3 = 6. Equalities can be reversed (Eq.symm), chained (Eq.trans),
and, most importantly, used to rewrite: if a = b and P a, then P b.
This last operation is Eq.subst, which is so common that it has its
own notation, ▸ (typed \t):
-/

example (a b : α) (h : a = b) : b = a := Eq.symm h

example (a b c : α) (h₁ : a = b) (h₂ : b = c) : a = c := Eq.trans h₁ h₂

example (a b : α) (h : a = b) (ha : P a) : P b := Eq.subst h ha

example (a b : α) (h : a = b) (ha : P a) : P b := h ▸ ha

example (f : α → α) (a b : α) (h : a = b) : f a = f b := congrArg f h

/-
The subscripts in h₁ are typed \1, \2, and so on.

    (*) rfl only works when both sides are equal by definition, i.e.,
    when Lean can unfold the definitions and reach the same term.
    Addition of natural numbers is defined by recursion on the second
    argument, so n + 0 = n holds by rfl, but 0 + n = n does not: it
    needs a proof by induction. In 1.2 we will see tactics
    that take care of these things for us.
-/

example (a b c : α) (h₁ : a = b) (h₂ : c = b) : a = c := h₂.symm ▸ h₁

example (a b : α) (h : a = b) (hb : P b) : P a := sorry

example (a : α) : ∃ x, x = a := sorry

example (f : α → α) (hf : ∀ x, f x = x) (a b : α) (h : a = b) :
    f a = b := sorry

example (f : α → α) (hf : ∀ x, f x = x) (a : α) (ha : P a) :
    P (f a) := (hf a).symm ▸ ha

/-
    (**) How is = defined in Lean? Hover over = or try #print Eq. You
    will find, essentially, the following definition:

        inductive Eq : α → α → Prop
          | refl (a : α) : Eq a a

    (and a = b is notation for Eq a b). This says that, for each pair
    of terms a b : α, Eq a b is a proposition, and that the only way
    to build a proof of it is Eq.refl a, a proof of a = a. In other
    words, a = b can only be proven when a and b are the same term (up
    to computation). This is what rfl is: it is just Eq.refl applied
    to the right term.

    We will see more inductive types later in the course. For now,
    the important point is that defining Eq like this automatically
    gives us a way to use equalities, which is essentially Eq.subst:
    to prove motive b from a = b, it is enough to prove motive a.
    This is Leibniz's principle: equal terms satisfy the same
    properties. Everything else follows from it. For instance, this
    is Eq.symm:
-/

example (a b : α) (h : a = b) : b = a :=
  Eq.subst (motive := fun x => x = a) h (Eq.refl a)

/-
    Here (motive := ...) tells Lean which property we are rewriting
    in, namely "x = a". Since a = a holds by Eq.refl, and a = b, we
    get b = a. Try to prove Eq.trans and congrArg in the same way!
-/

end
