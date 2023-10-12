import LeanCourse.Common
open Real
noncomputable section
set_option linter.unusedVariables false

/- # Last Lecture -/

/- You type code on the left-hand side of the screen,
  and Lean automatically compiles the file and
  shows output in the *Lean Infoview* on the right.

  If you ever close the Infoview, you can press
  `ctrl+shift+enter` (or `cmd+shift+enter` on a Mac)
  to reopen it -/

/- Every expression in Lean has a type,
  and when applying a function to an argument,
  the argument must lie in the domain of the function.  -/
#check 1
#check fun x : ℝ ↦ x^2
#check (fun x : ℝ ↦ x^2) (π + 3)

/- Statements have type `Prop` and predicates on `A` have type `A → Prop`. -/
#check 3 < π
#check (Nat.Prime)


/- To prove a statement, you use *tactics* to construct a proof of that statement. -/

example : 2 + 2 = 4 := by rfl

example : 2 + 2 = 4 := by
  rfl

example : 2 + 2 = 4 := by {
  rfl
}






/- # Rewriting

`rw` (short for "rewrite") is a tactic that changes a part of a goal to something equal to it.
-/

example (a b c : ℝ) : a * b * c = b * (a * c) := sorry


/-
In the following lemma the commutator of two elements of a group is defined as
`⁅g, h⁆ = g * h * g ⁻¹ * h ⁻¹`
-/

section
variable {G : Type} [Group G] (g h : G)

#check commutatorElement_def g h
#check mul_inv_rev g h

lemma inverse_of_a_commutator : ⁅g, h⁆⁻¹ = ⁅h, g⁆ := by sorry

end



/-
Variants of `rw`:
* `rw [lemma1, lemma2, ...]` is short for multiple rewrites in a row
* `rw [← my_lemma]` to rewrite `my_lemma` from right to left
* `rw [my_lemma] at h` to rewrite using `my_lemma` at `h`.
You have to know what lemma you need to rewrite with.
-/

example (a b c d : ℝ) (h : c = a*d - 1) (h' : b = a*d) : c = b - 1 := by sorry

/-
# Calculational proofs using `calc`
-/

example (a b c d : ℝ) (h : a + c = b*a - d) (h' : d = a*b) : a + c = 0 := sorry





/- There are more advanced tactics that will do particular kinds of calculations.
* `ring`: prove equalities in commutative rings
* `linarith`: prove linear (in)equalities -/

variable {R : Type} [CommRing R] (a b : R)
example : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring

example (a b c : ℝ) (h1 : 2 * a ≤ 3 * b) (h2 : 1 ≤ a) (h3 : c = 2) :
    c + a ≤ 5 * b := by linarith




/-
**Backwards reasoning** is where we chain implications backwards, deducing
what we want to prove from a combination of other statements (potentially even stronger ones).
-/

lemma simple_proof (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by sorry



/- We can prove the following manually, or using more advanced tactics. -/

example : Continuous (fun x ↦ 2 + x * Real.sin x) := by sorry

/- `apply?` can give suggestions what lemmas you could apply. -/


/-
# Difference between `rw` and `apply`
- `rw` can take place almost anywhere in the goal, but `apply` has to match the outermost thing you are trying to prove
- *generally* you `rw` with an equality, and `apply` anything else.
-/




/- In the following lemma, notice that `a`, `b`, `c`
  are inside curly braces `{...}`.
  This means that these arguments are *implicit*:
  they don't have to be stated, but will be figured out by Lean automatically. -/

lemma my_lemma {a b c : ℝ} (h : a + b = a + c) : b = c :=
    add_left_cancel h

example {b c : ℝ} (h : 2 + b = 2 + c) : b = c := sorry -- prove using `my_lemma`