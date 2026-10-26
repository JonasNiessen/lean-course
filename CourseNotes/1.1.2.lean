/- 1.1.2 Dependent type theory -/

/-
In set theory everything is a set. Lean is based on type theory:
everything is a term, and every term has a type. You can ask Lean for
the type of a term with the command #check.

Where do we see the answer? Lean constantly reads your file while you
type, and talks back to you through the infoview, the panel on the
right of the editor (in VS Code, if it is not there, open it with
Ctrl+Shift+Enter, or from the ∀ menu at the top right). The infoview
shows the information about the line where your cursor is:
    - the output of commands such as #check or #eval,
    - errors and warnings, which are also underlined in the file (red
      for errors, yellow for warnings, blue for information),
    - and, once we start writing proofs with tactics in 1.2, the goal,
      i.e., what is left to prove. You will be looking at it all the
      time!
Put your cursor on each of the following lines and look at the infoview:
-/

#check 2                      -- Nat
#check (2 : Int)              -- Int
#check "Aachen"               -- String
#check Nat → Nat              -- Type
#check fun (n : Nat) => n + 1 -- Nat → Nat

/-
A few remarks:
    - Nat is the type of the natural numbers. Int of the integers.
    - The arrow → is typed \to. Most unicode symbols in Lean are typed
      with a backslash followed by a descriptive name (like in LaTeX).
    - (2 : Int) means "the term 2, of type Int". Unlike in set theory,
      the natural number 2 and the integer 2 are different terms,
      since every term has exactly one type.
    - fun (n : Nat) => n + 1 is the function n ↦ n + 1. Functions
      between two types form again a type, Nat → Nat.
    - Types are terms as well, so they also have a type: Nat : Type.

Lean can also compute with #eval, and we can name terms with def:
-/

def double (n : Nat) : Nat := 2 * n

#check double     -- double (n : Nat) : Nat
#eval double 21   -- 42

/-
Thus def is a way to define a named function, while fun is a way to
define an anonymous function.
-/

/-
To be precise, Lean is not based on type theory, but on a particular
kind of dependent type theory.
What does "dependent" mean? It means that types can depend on terms.
For instance, for every n : Nat there is a type Fin n, whose terms are
the natural numbers smaller than n (with arithmetic modulo n).
-/

#check Fin 5            -- Type
#check (3 : Fin 5)      -- Fin 5
#eval (3 : Fin 5) + 4   -- 2

/-
So Fin is a function that takes a term n and returns a type. And we
can have functions whose output type depends on the input. Such a
function is called a dependent function, and its type is written
(n : Nat) → Fin (n + 1):
-/

def zeroFin (n : Nat) : Fin (n + 1) := 0

#check zeroFin    -- zeroFin (n : Nat) : Fin (n + 1)

/-
This may look like a technicality, but it is what makes Lean
expressive enough to talk about mathematics: "for all n, ..." will
turn out to be precisely a dependent function. More on this in 1.1.3.

    (*) If Nat : Type, what is the type of Type? It is Type 1, whose
    type is Type 2, and so on. These are called universes. If we had
    Type : Type, we could reproduce Russell's paradox (or rather, its
    type theoretic version, Girard's paradox). In practice, most of the time you
    can forget about universes.
-/
