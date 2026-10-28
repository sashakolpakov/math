import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Free

/-! # Differential Rank Tower -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DifferentialRankTower.Construction

noncomputable section

/-! Bounds on differential rank in finite field extensions for the Openness
inseparability argument. -/

open KaehlerDifferential _root_.Module IntermediateField
open scoped TensorProduct IntermediateField

/-- Differential ranks are subadditive in a tower of finite extensions. -/
theorem finrank_kaehler_le_tower
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [Module.Finite K E] [Module.Finite E L] :
    Module.finrank L Ω[L⁄K] ≤ Module.finrank E Ω[E⁄K] + Module.finrank L Ω[L⁄E] := by
  have : Module.Finite K L := Module.Finite.trans E L
  let f := mapBaseChange K E L
  let g := KaehlerDifferential.map K E L L
  have hdim := LinearMap.finrank_range_add_finrank_ker g
  have hsurj : g.range = ⊤ := LinearMap.range_eq_top.mpr (map_surjective K E L)
  have hker : g.ker = f.range := (range_mapBaseChange K E L).symm
  rw [hsurj, finrank_top, hker] at hdim
  have hle := f.finrank_range_le
  rw [Module.finrank_baseChange] at hle
  omega

/-- Differentials of a monogenic field extension are spanned by the
differential of its generator. -/
theorem span_differential_powerBasis
    (K L : Type*) [Field K] [Field L] [Algebra K L] (b : PowerBasis K L) :
    Submodule.span L {D K L b.gen} = ⊤ := by
  apply top_unique
  rw [← span_range_derivation K L, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨q, rfl⟩ := b.exists_eq_aeval' x
  rw [(D K L).map_aeval]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- A monogenic extension has differential dimension at most one. -/
theorem finrank_kaehler_powerBasis_le_one
    (K L : Type*) [Field K] [Field L] [Algebra K L] (b : PowerBasis K L) :
    Module.finrank L Ω[L⁄K] ≤ 1 := by
  have h := finrank_span_le_card (R := L) ({D K L b.gen} : Set Ω[L⁄K])
  rw [span_differential_powerBasis K L b, finrank_top] at h
  simpa using h

/-- A nonseparable finite extension in characteristic p has inseparable
degree at least p. -/
theorem prime_le_finInsepDegree_of_not_isSeparable
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (h : ¬ Algebra.IsSeparable K L) :
    p ≤ Field.finInsepDegree K L := by
  obtain ⟨r, hr⟩ := finInsepDegree_eq_pow K L p
  have hr0 : r ≠ 0 := by
    intro hz
    apply h
    apply (isSeparable_iff_finInsepDegree_eq_one K L).mpr
    simpa [hz] using hr
  rw [hr]
  exact le_trans (by simp) (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.one_le_iff_ne_zero.mpr hr0))

/-- The differential rank bound for a simple extension, in exponential form. -/
theorem pow_finrank_kaehler_le_finInsepDegree_powerBasis
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (b : PowerBasis K L) (p : ℕ) [Fact p.Prime] [CharP K p] :
    p ^ Module.finrank L Ω[L⁄K] ≤ Field.finInsepDegree K L := by
  have : Module.Finite K L := b.finite
  by_cases hsep : Algebra.IsSeparable K L
  · have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    simp only [Module.finrank_zero_of_subsingleton, pow_zero]
    exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  · exact (Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (finrank_kaehler_powerBasis_le_one K L b)).trans
      (by simpa using prime_le_finInsepDegree_of_not_isSeparable K L p hsep)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DifferentialRankTower.Construction
