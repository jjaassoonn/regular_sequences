import Mathlib.LinearAlgebra.Quotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Logic.UnivLE
import Mathlib.Data.Fin.VecNotation

universe uR uM

suppress_compilation

open Pointwise

variable [UnivLE.{uR, uM}] -- Future-proof?
variable (R : Type uR) (M : Type uM)
variable [CommRing R] [AddCommGroup M] [Module R M]

/-
A pre-regular sequence is just a list of elements of `R`, `[f_0, f_1, ..., f_r]`

## Implementation notes
This is a structure for the following reasons
1. to enable dot notation for `quotientFactor` later. Presumably `List.quotientFactor` is not very useful.
2. so that we can make `M` appear explicitly in type signature.
-/
structure PreRegularSequence (R : Type uR) (M : Type uM) : Type uR where
  toList : List R

namespace PreRegularSequence

variable (s : PreRegularSequence R M)

variable {R M}

/--
Let `f_0, ..., f_r` be a sequence. The `i`-th quotient factor is `M ⧸ {f_0, ..., f_{i - 1}} • M`.

`0`-th is `M ⧸ ⟨f_0⟩`
`1`-st is `M ⧸ ⟨f_0⟩`
`2`-nd is `M ⧸ ⟨f_0, f_1⟩`

length of the list is `r + 1`
Note that the `r+1`-st quotient factor is `M ⧸ ⟨f_0, ..., f_{r-1}⟩`
-/
def quotientFactor (i : ℕ) : Type uM :=
  M ⧸ Ideal.span { x : R | x ∈ s.toList.take i } • (⊤ : Submodule R M)

instance (i : ℕ) : AddCommGroup (s.quotientFactor i) :=
  inferInstanceAs <| AddCommGroup <| M ⧸ _

instance (i : ℕ) : Module R (s.quotientFactor i) :=
  inferInstanceAs <| Module R (M ⧸ _)

end PreRegularSequence

open scoped nonZeroSMulDivisors

/--
An `M`-regular sequence `f_0, ..., f_r` is a list such that

* for `i = 0, ..., r-1`, `f_i` is a nonzero-smul-divisor in `M ⧸ ⟨f_0, ..., f_{i-1}⟩`
* `M ⧸ ⟨f_0, ..., f_r⟩` is not zero
-/
structure RegularSequence extends PreRegularSequence R M where
  /-- For `i = 0, ..., r`, for `i = 0, ..., r-1`, `f_i` is a nonzero-smul-divisor in `M ⧸ ⟨f_0, ..., f_{i-1}⟩` -/
  regular : ∀ (i : ℕ) (h : i < toList.length), toList.nthLe i h ∈ R⁰[toPreRegularSequence.quotientFactor i]
  /-- `M ⧸ ⟨f_0, ..., f_r⟩` is not zero. -/
  nontrivial : Nontrivial <| toPreRegularSequence.quotientFactor toList.length

attribute [instance] RegularSequence.nontrivial

namespace RegularSequence

instance [Nontrivial M] : EmptyCollection (RegularSequence R M) where
  emptyCollection :=
    { toList := ∅
      regular := fun i h ↦ by simp at h
      nontrivial := by
        obtain ⟨x, y, h⟩ : Nontrivial M := by infer_instance
        refine ⟨Submodule.Quotient.mk x, Submodule.Quotient.mk y, fun r ↦ ?_⟩
        rw [Submodule.Quotient.eq] at r
        simp only [List.empty_eq, List.length_nil, Nat.pred_zero, List.take_nil, List.find?_nil,
          List.not_mem_nil, Set.setOf_false, Ideal.span_empty, Submodule.bot_smul,
          Submodule.mem_bot] at r
        exact h (sub_eq_zero.mp r) }

-- Interestingly or uninterestingly, if `R` is zero ring, then `X₀, X₁` is not a regular sequence.
open MvPolynomial in
/--
Consider `S = R[X_0, X_1]`, then `[X_0, X_1]` is a regular sequence.

* regularity: `X_0 ∈ S⁰_{R[X_0, X_1] ⧸ ∅}` and `X_1 ∈ S⁰_{R[X_0, X_1] ⧸ ⟨X_0⟩}`
* nontrivial `R[X_0, X_1] ⧸ ⟨X_0, X_1⟩ ≠ 0`
-/
example (k : Type*) [Field k] :
    RegularSequence (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k) where
  toList := [X 0, X 1]
  regular i h := by
    classical
    rw [List.length_cons, List.length_singleton, show Nat.succ 1 = 2 from rfl] at h
    interval_cases i
    · rintro x (hx : X 0 • _ = 0)
      induction' x using Quotient.inductionOn' with p
      change Submodule.Quotient.mk (X 0 * p) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      simp only [Nat.pred_zero, List.take_zero, List.find?_nil, List.not_mem_nil, Set.setOf_false,
        Ideal.span_empty, smul_eq_mul, Ideal.mul_top, Ideal.mem_bot, isRegular_X, IsRegular.left,
        IsLeftRegular.mul_left_eq_zero_iff] at hx
      subst p
      rfl
    · rintro x (hx : X 1 • _ = 0)
      induction' x using Quotient.inductionOn' with p
      change Submodule.Quotient.mk _ = 0 at hx ⊢
      rw [Submodule.Quotient.mk_eq_zero] at hx ⊢
      simp only [smul_eq_mul, List.take_cons_succ, List.take_zero, List.mem_singleton,
        Set.setOf_eq_eq_singleton, Ideal.mul_top] at hx ⊢
      suffices H : X 1 ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}
      · have prime_X0 := (Ideal.span_singleton_prime (α := MvPolynomial (Fin 2) k) (p := X 0) ?_).mpr sorry
        exact ((prime_X0.mul_mem_iff_mem_or_mem (x := X 1) (y := p)).mp hx).resolve_left H
        · exact (by simpa only [coeff_X', ite_true, coeff_zero, one_ne_zero] using
            (ext_iff _ _).mp · (fun₀ | 0 => 1))

      intro H
      rw [Ideal.mem_span_singleton] at H
      -- H : X₀ ∣ X₁, there is a contradiction here somewhere
      obtain ⟨q, hq⟩ := H
      sorry
  nontrivial := by
    delta PreRegularSequence.quotientFactor
    simp only [List.length_cons, List.length_singleton, List.take_cons_succ, List.take_nil,
      Bool.not_eq_true, List.mem_cons, List.mem_singleton, smul_eq_mul, Ideal.mul_top,
      List.find?_nil, List.not_mem_nil, or_false]
    suffices e : (MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1}) ≃ₗ[k] k
    · exact ⟨e.symm 0, e.symm 1, fun h ↦ zero_ne_one <| e.symm.injective h⟩
    sorry

end RegularSequence
