import OAI.RepresentationTheory.Theta.Geometric.Period.DualLattice
import Mathlib.GroupTheory.OrderOfElement

/-! # Dual Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The discriminant group of the actual period lattice has exactly
the prescribed doubled elementary divisors. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.periodDualReferenceEquiv (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    D.periodDualLattice hg x ≃ₗ[ℤ] (D.pel.reference.lattice →ₗ[ℤ] ℤ) :=
  (D.periodDualLatticeEquiv hg x).trans (D.periodLatticeEquiv hg x).dualMap

def Data.ActiveHeckeThetaData.periodLatticeDualInclusion (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    D.pel.reference.lattice →ₗ[ℤ] D.periodDualLattice hg x :=
  (Submodule.inclusion (D.periodLattice_le_dual hg x)).comp
    (D.periodLatticeEquiv hg x).toLinearMap

theorem Data.ActiveHeckeThetaData.periodDualReferenceEquiv_inclusion (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (u : D.pel.reference.lattice) :
    D.periodDualReferenceEquiv hg x (D.periodLatticeDualInclusion hg x u) =
      D.pel.reference.integralForm u := by
  ext v
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ)
    (LinearMap.BilinForm.dualSubmoduleParing (D.periodImaginaryForm hg x)
      (D.periodLatticeDualInclusion hg x u) (D.periodLatticeEquiv hg x v)) = _
  exact (LinearMap.BilinForm.dualSubmoduleParing_spec (D.periodImaginaryForm hg x)
    (D.periodLatticeDualInclusion hg x u) (D.periodLatticeEquiv hg x v)).trans
      (D.periodImaginaryForm_integral hg x u v)

def Data.ActiveHeckeThetaData.periodDiscriminantEquiv (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    (D.periodDualLattice hg x ⧸ (D.periodLatticeDualInclusion hg x).range) ≃ₗ[ℤ]
      ((D.pel.reference.lattice →ₗ[ℤ] ℤ) ⧸ D.pel.reference.integralForm.range) :=
  Submodule.Quotient.equiv _ _ (D.periodDualReferenceEquiv hg x) (by
    rw [← LinearMap.range_comp]
    congr 1
    ext u v
    exact LinearMap.congr_fun (D.periodDualReferenceEquiv_inclusion hg x u) v)

theorem Data.ActiveHeckeThetaData.periodDiscriminant_type (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Nonempty ((D.periodDualLattice hg x ⧸ (D.periodLatticeDualInclusion hg x).range) ≃+
      ((∀ i : Fin (3 * s), ZMod (D.pel.reference.polarizationType i)) ×
        (∀ i : Fin (3 * s), ZMod (D.pel.reference.polarizationType i)))) := by
  rcases hg.reference_admissible with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _⟩
  exact ⟨(D.periodDiscriminantEquiv hg x).toAddEquiv.trans ht.some⟩

theorem Data.ActiveHeckeThetaData.periodDiscriminant_finite (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Finite (D.periodDualLattice hg x ⧸ (D.periodLatticeDualInclusion hg x).range) := by
  rcases hg.reference_admissible with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
  let (i : Fin (3 * s)) : NeZero (D.pel.reference.polarizationType i) := ⟨ne_of_gt (hpos i)⟩
  exact Finite.of_equiv _ (D.periodDiscriminant_type hg x).some.toEquiv.symm

theorem Data.ActiveHeckeThetaData.periodDualLattice_bounded_denominator (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    ∃ n : ℕ, 0 < n ∧ ∀ v : D.periodDualLattice hg x,
      n • v.val ∈ (D.canonicalPeriodData hg x).periodIntegerLattice := by
  let Q := D.periodDualLattice hg x ⧸ (D.periodLatticeDualInclusion hg x).range
  let := D.periodDiscriminant_finite hg x
  refine ⟨Nat.card Q, Nat.card_pos, ?_⟩
  intro v
  have hz : (Submodule.Quotient.mk (Nat.card Q • v) : Q) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact card_nsmul_eq_zero'
  obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hv := congrArg Subtype.val hu
  change (D.periodLatticeEquiv hg x u).val = Nat.card Q • v.val at hv
  exact hv ▸ (D.periodLatticeEquiv hg x u).property

end

end OAI.RepresentationTheory.Theta.Geometric
