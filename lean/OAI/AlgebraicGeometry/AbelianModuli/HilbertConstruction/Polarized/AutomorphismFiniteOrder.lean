import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismsFiniteOverField
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.UnitSubgroup
import Mathlib.GroupTheory.OrderOfElement

/-! # Automorphism Finite Order -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual endomorphism-ring unit of every polarized full-level automorphism over a field has finite multiplicative order. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem Polarized.AutomorphismFiniteOrder.polarizedAutomorphismUnitSubgroup_finite : Finite A.automorphismUnitSubgroup := by
  have := Polarized.AutomorphismsFiniteOverField.polarizedAutomorphisms_finite_overField A
  exact Finite.of_surjective (Moduli.Isomorphisms.LevelPreservingIso.automorphismUnit (A := A))
    Moduli.Isomorphisms.LevelPreservingIso.automorphismUnit_surjective

theorem Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_isOfFinOrder (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    IsOfFinOrder e.endRingUnit := by
  have := Polarized.AutomorphismFiniteOrder.polarizedAutomorphismUnitSubgroup_finite A
  obtain ⟨m, hm, he⟩ := (isOfFinOrder_of_finite e.automorphismUnit).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, congrArg Subtype.val he⟩

theorem Moduli.Isomorphisms.LevelPreservingIso.endRingUnit_exists_positive_power (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    ∃ m : ℕ, 0 < m ∧ e.endRingUnit.val ^ m = 1 := by
  obtain ⟨m, hm, he⟩ := (e.endRingUnit_isOfFinOrder A).exists_pow_eq_one
  exact ⟨m, hm, congrArg Units.val he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
