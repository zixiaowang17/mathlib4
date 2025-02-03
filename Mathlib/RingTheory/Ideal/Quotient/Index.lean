/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Finsupp.Fintype
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.TensorProduct
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Indices of ideals

## Main result
- `Submodule.finite_quotient_smul`:
  Let `N` be a finite index f.g. `R`-submodule, and `I` be a finite index ideal.
  Then `I • N` also has finite index.
- `Ideal.index_quotient_pow_le`:
  If `I` is generated by `k` elements,
  the index of `I ^ n` is bounded by `#(R ⧸ I) ^ (k⁰ + k¹ + ⋯ + kⁿ⁻¹)`.

-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (I : Ideal R) {N : Submodule R M}

open TensorProduct in
/-- Let `N` be a finite index f.g. `R`-submodule, and `I` be a finite index ideal.
Then `I • N` also has finite index. -/
lemma Submodule.finite_quotient_smul [Finite (R ⧸ I)] [Finite (M ⧸ N)] (hN : N.FG) :
    Finite (M ⧸ I • N) := by
  suffices (I • N).toAddSubgroup.FiniteIndex by
    exact (I • N).toAddSubgroup.finite_quotient_of_finiteIndex
  suffices Nat.card (N ⧸ (I • N).comap N.subtype) ≠ 0 by
    constructor
    rw [← AddSubgroup.relindex_mul_index
      (H := (I • N).toAddSubgroup) (K := N.toAddSubgroup) Submodule.smul_le_right]
    have inst : Finite (M ⧸ N.toAddSubgroup) := ‹_›
    exact mul_ne_zero this AddSubgroup.index_ne_zero_of_finite
  let e : (N ⧸ (I • N).comap N.subtype) ≃ₗ[R] (R ⧸ I) ⊗[R] N :=
    Submodule.quotEquivOfEq _ (I • (⊤ : Submodule R N)) (Submodule.map_injective_of_injective
      N.injective_subtype (by simp [Submodule.smul_le_right])) ≪≫ₗ
        (quotTensorEquivQuotSMul N I).symm
  rw [Nat.card_congr e.toEquiv]
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have : Finite ((R ⧸ I) ⊗[R] N) := Module.finite_of_finite (R ⧸ I)
  exact Nat.card_pos.ne'

-- We have `hs` and `N` instead of using `span R s` in the goal to make it easier to use.
-- Usually we would like to bound the index of some abstract `I • N`, and we may construct `s` while
-- applying this lemma instead of having to provide it beforehand.
open TensorProduct in
lemma Submodule.index_smul_le [Finite (R ⧸ I)]
    (s : Finset M) (hs : Submodule.span R s = N) :
    (I • N).toAddSubgroup.index ≤ I.toAddSubgroup.index ^ s.card * N.toAddSubgroup.index := by
  classical
  cases nonempty_fintype (R ⧸ I)
  rw [← AddSubgroup.relindex_mul_index
    (H := (I • N).toAddSubgroup) (K := N.toAddSubgroup) Submodule.smul_le_right]
  gcongr
  show (Nat.card (N ⧸ (I • N).comap N.subtype)) ≤ Nat.card (R ⧸ I) ^ s.card
  let e : (N ⧸ (I • N).comap N.subtype) ≃ₗ[R] (R ⧸ I) ⊗[R] N :=
    Submodule.quotEquivOfEq _ (I • (⊤ : Submodule R N)) (Submodule.map_injective_of_injective
      N.injective_subtype (by simp [Submodule.smul_le_right])) ≪≫ₗ
      (quotTensorEquivQuotSMul N I).symm
  rw [Nat.card_congr e.toEquiv]
  have H : LinearMap.range (Finsupp.linearCombination R (α := s) (↑)) = N := by
    rw [Finsupp.range_linearCombination, ← hs, Subtype.range_val]; rfl
  let f : (s →₀ R) →ₗ[R] N := (Finsupp.linearCombination R (↑)).codRestrict _
    (Set.range_subset_iff (s := N.carrier).mp <| by exact H.le)
  have hf : Function.Surjective f := fun x ↦ by
    obtain ⟨y, hy⟩ := H.ge x.2; exact ⟨y, Subtype.ext hy⟩
  have : Function.Surjective
      (f.lTensor (R ⧸ I) ∘ₗ (finsuppScalarRight R (R ⧸ I) s).symm.toLinearMap) :=
    (LinearMap.lTensor_surjective (R ⧸ I) hf).comp (LinearEquiv.surjective _)
  refine (Nat.card_le_card_of_surjective _ this).trans ?_
  simp only [Nat.card_eq_fintype_card, Fintype.card_finsupp, Fintype.card_coe, le_rfl]

variable {I}

lemma Ideal.finite_quotient_pow (hI : I.FG) [Finite (R ⧸ I)] (n) : Finite (R ⧸ I ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    infer_instance
  | succ n _ =>
    exact Submodule.finite_quotient_smul (I ^ n) hI

lemma Ideal.index_pow_le
    (s : Finset R) (hs : Ideal.span s = I) [Finite (R ⧸ I)] (n) :
    (I ^ n).toAddSubgroup.index ≤ I.toAddSubgroup.index ^ ∑ i ∈ Finset.range n, s.card ^ i := by
  have := Ideal.finite_quotient_pow ⟨s, hs⟩
  induction n with
  | zero =>
    simp
  | succ n IH =>
    refine (Submodule.index_smul_le (I ^ n) s hs).trans ?_
    refine (Nat.mul_le_mul (Nat.pow_le_pow_left IH _) le_rfl).trans ?_
    rw [← pow_mul, ← pow_succ, geom_sum_succ, mul_comm]
