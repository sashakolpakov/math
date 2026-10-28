import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor
import OAI.RepresentationTheory.Theta.Geometric.IntegralDualLattice
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Integral Dual Le -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

section

/-! The imaginary part of the actual ThetaConstruction Riemann form gives a
nondegenerate real pairing. Its integral dual is a constructed full
discrete lattice, canonically identified with the integer dual. -/

section
open OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor.Geometric

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E)

def DefinitionsIntegral.MarkedPolarizedTorus.imaginaryForm : LinearMap.BilinForm ℝ (DefinitionsIntegral.Tangent g) where
  toFun u := Complex.imCLM.toLinearMap.comp ((T.riemannForm u).restrictScalars ℝ)
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (T.riemannForm (u + v) w).im = (T.riemannForm u w).im + (T.riemannForm v w).im
    rw [map_add, LinearMap.add_apply, Complex.add_im]
  map_smul' r u := by
    apply LinearMap.ext
    intro v
    change (T.riemannForm (r • u) v).im = r * (T.riemannForm u v).im
    have hr : r • u = (r : ℂ) • u := (IsScalarTower.algebraMap_smul ℂ r u).symm
    rw [hr, map_smulₛₗ, LinearMap.smul_apply]
    simp

theorem DefinitionsIntegral.MarkedPolarizedTorus.imaginaryForm_skew (u v : DefinitionsIntegral.Tangent g) : T.imaginaryForm v u = -T.imaginaryForm u v := by
  change (T.riemannForm v u).im = -(T.riemannForm u v).im
  rw [T.hermitian]
  rfl

theorem DefinitionsIntegral.MarkedPolarizedTorus.imaginaryForm_nondegenerate : T.imaginaryForm.Nondegenerate := by
  have hleft : T.imaginaryForm.SeparatingLeft := by
    intro u hu
    by_contra hne
    have hz := hu (Complex.I • u)
    have hpos := T.positive u hne
    change (T.riemannForm u (Complex.I • u)).im = 0 at hz
    rw [map_smul] at hz
    simp only [smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add] at hz
    exact (ne_of_gt hpos) hz
  refine ⟨hleft, ?_⟩
  intro u hu
  apply hleft u
  intro v
  rw [T.imaginaryForm_skew v u, hu v, neg_zero]

def DefinitionsIntegral.MarkedPolarizedTorus.integralDualLattice : Submodule ℤ (DefinitionsIntegral.Tangent g) :=
  T.imaginaryForm.dualSubmodule (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice

instance DefinitionsIntegral.MarkedPolarizedTorus.integralDualLattice_discrete : DiscreteTopology T.integralDualLattice :=
  RepresentationTheory.Theta.Geometric.IntegralDualLattice.dualLattice_discrete (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice
    (DefinitionsIntegral.Geometric.integralLatticeBasis T) T.imaginaryForm T.imaginaryForm_nondegenerate

instance DefinitionsIntegral.MarkedPolarizedTorus.integralDualLattice_full : IsZLattice ℝ T.integralDualLattice :=
  RepresentationTheory.Theta.Geometric.IntegralDualLattice.dualLattice_full (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice
    (DefinitionsIntegral.Geometric.integralLatticeBasis T) T.imaginaryForm T.imaginaryForm_nondegenerate

def DefinitionsIntegral.MarkedPolarizedTorus.integralDualEquiv : T.integralDualLattice ≃ₗ[ℤ]
    ((ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice →ₗ[ℤ] ℤ) :=
  RepresentationTheory.Theta.Geometric.IntegralDualLattice.integralDualLatticeEquiv (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice
    (DefinitionsIntegral.Geometric.integralLatticeBasis T) T.imaginaryForm T.imaginaryForm_nondegenerate

theorem DefinitionsIntegral.MarkedPolarizedTorus.lattice_le_integralDual : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice ≤ T.integralDualLattice := by
  intro u hu v hv
  exact Submodule.mem_one.mpr ⟨DefinitionsIntegral.Geometric.integralLatticeForm T ⟨u, hu⟩ ⟨v, hv⟩,
    (DefinitionsIntegral.Geometric.integralLatticeForm_riemann T ⟨u, hu⟩ ⟨v, hv⟩).symm⟩

def DefinitionsIntegral.MarkedPolarizedTorus.integralDualInclusion : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice →ₗ[ℤ] T.integralDualLattice :=
  Submodule.inclusion T.lattice_le_integralDual

theorem DefinitionsIntegral.MarkedPolarizedTorus.integralDualEquiv_inclusion (u v : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) :
    T.integralDualEquiv (T.integralDualInclusion u) v = DefinitionsIntegral.Geometric.integralLatticeForm T u v := by
  apply Int.cast_injective (α := ℝ)
  exact (T.imaginaryForm.dualSubmoduleParing_spec (T.integralDualInclusion u) v).trans
    (DefinitionsIntegral.Geometric.integralLatticeForm_riemann T u v)

end

namespace IntegralDualLe.Geometric.MarkedPolarizedTorus

end IntegralDualLe.Geometric.MarkedPolarizedTorus

end

section

/-! The original lattice has finite index in its integral dual.
The finite discriminant group supplies an actual positive common
denominator, without assuming a polarization type or dual variety. -/

section
open OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor.Geometric

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E)

theorem DefinitionsIntegral.MarkedPolarizedTorus.integralDualInclusion_injective : Function.Injective T.integralDualInclusion := by
  intro u v h
  apply Subtype.ext
  exact congrArg (fun w : T.integralDualLattice => w.val) h

instance DefinitionsIntegral.MarkedPolarizedTorus.integralDualDiscriminant_finite : Finite (T.integralDualLattice ⧸ T.integralDualInclusion.range) := by
  let : Module.Free ℤ T.integralDualLattice := ZLattice.module_free ℝ T.integralDualLattice
  let : Module.Finite ℤ T.integralDualLattice := ZLattice.module_finite ℝ T.integralDualLattice
  apply Submodule.finiteQuotientOfFreeOfRankEq
  rw [LinearMap.finrank_range_of_inj T.integralDualInclusion_injective,
    ZLattice.rank ℝ (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice,
    ZLattice.rank ℝ T.integralDualLattice]
  rfl

def DefinitionsIntegral.MarkedPolarizedTorus.integralDualDiscriminantEquiv :
    (T.integralDualLattice ⧸ T.integralDualInclusion.range) ≃ₗ[ℤ]
      (((ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice →ₗ[ℤ] ℤ) ⧸ (DefinitionsIntegral.Geometric.integralLatticeForm T).range) :=
  Submodule.Quotient.equiv _ _ T.integralDualEquiv (by
    let φ : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice →ₗ[ℤ]
        ((ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice →ₗ[ℤ] ℤ) := DefinitionsIntegral.Geometric.integralLatticeForm T
    have hcomp : T.integralDualEquiv.toLinearMap.comp T.integralDualInclusion = φ := by
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      exact T.integralDualEquiv_inclusion u v
    exact (LinearMap.range_comp T.integralDualInclusion T.integralDualEquiv.toLinearMap).symm.trans
      (congrArg LinearMap.range hcomp))

theorem DefinitionsIntegral.MarkedPolarizedTorus.integralDual_bounded_denominator :
    ∃ n : ℕ, 0 < n ∧ ∀ v : T.integralDualLattice,
      n • v.val ∈ (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice := by
  let Q := T.integralDualLattice ⧸ T.integralDualInclusion.range
  refine ⟨Nat.card Q, Nat.card_pos, ?_⟩
  intro v
  have hz : (Submodule.Quotient.mk (Nat.card Q • v) : Q) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact card_nsmul_eq_zero'
  obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have h := congrArg Subtype.val hu
  change u.val = Nat.card Q • v.val at h
  exact h ▸ u.property

end

namespace IntegralDualLe.Geometric.MarkedPolarizedTorus

end IntegralDualLe.Geometric.MarkedPolarizedTorus

end

/-! The actual integral dual lattice forms a projective complex torus.
A positive common denominator makes the original Hermitian form integral
on the dual lattice and constructs its projective period data. -/

section
open OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationFactor.Geometric

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E)

theorem DefinitionsIntegral.MarkedPolarizedTorus.integralDual_positive_integral :
    ∃ H : DefinitionsIntegral.Tangent g →ₗ⋆[ℂ] DefinitionsIntegral.Tangent g →ₗ[ℂ] ℂ,
      (∀ u v, H v u = star (H u v)) ∧
      (∀ u, u ≠ 0 → 0 < (H u u).re) ∧
      (∀ u ∈ T.integralDualLattice, ∀ v ∈ T.integralDualLattice,
        ∃ m : ℤ, (H u v).im = (m : ℝ)) := by
  obtain ⟨n, hn, hL⟩ := T.integralDual_bounded_denominator
  refine ⟨(n * n) • T.riemannForm, ?_, ?_, ?_⟩
  · intro u v
    change (n * n) • T.riemannForm v u = star ((n * n) • T.riemannForm u v)
    rw [T.hermitian, star_nsmul]
  · intro u hu
    change (((n * n) • T.riemannForm u u) : ℂ).re > 0
    rw [Complex.re_nsmul, nsmul_eq_mul]
    exact mul_pos (Nat.cast_pos.mpr (Nat.mul_pos hn hn)) (T.positive u hu)
  · intro u hu v hv
    let a : T.lattice := ⟨n • u, hL ⟨u, hu⟩⟩
    let b : T.lattice := ⟨n • v, hL ⟨v, hv⟩⟩
    have he := DefinitionsIntegral.Geometric.integralLatticeForm_riemann T a b
    refine ⟨DefinitionsIntegral.Geometric.integralLatticeForm T a b, ?_⟩
    have hscale : T.riemannForm (n • u) (n • v) = (n * n) • T.riemannForm u v := by
      have hfirst := congrArg (fun l : DefinitionsIntegral.Tangent g →ₗ[ℂ] ℂ => l (n • v))
        (map_nsmul T.riemannForm.toAddMonoidHom n u)
      have hsecond := map_nsmul (T.riemannForm u).toAddMonoidHom n v
      exact hfirst.trans ((congrArg (fun w : ℂ => n • w) hsecond).trans (smul_smul n n _))
    exact (congrArg Complex.im hscale).symm.trans he

instance DefinitionsIntegral.MarkedPolarizedTorus.integralDualTorus_compact : CompactSpace ((DefinitionsIntegral.Tangent g) ⧸ T.integralDualLattice.toAddSubgroup) := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic T.integralDualLattice
    (QuotientAddGroup.mk : DefinitionsIntegral.Tangent g → (DefinitionsIntegral.Tangent g) ⧸ T.integralDualLattice.toAddSubgroup)
    QuotientAddGroup.continuous_mk (by
      intro u v hv
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff v).mpr hv, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

local instance DefinitionsIntegral.MarkedPolarizedTorus.integralDual_addSubgroup_discrete : DiscreteTopology T.integralDualLattice.toAddSubgroup :=
  T.integralDualLattice_discrete

def DefinitionsIntegral.MarkedPolarizedTorus.integralDualPeriodData : RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData where
  space := DefinitionsIntegral.Tangent g
  periodIntegerLattice := T.integralDualLattice
  periodIntegerLattice_discrete := T.integralDualLattice_discrete
  periodIntegerLattice_full := T.integralDualLattice_full
  projective := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (DefinitionsIntegral.Tangent g)
    T.integralDualLattice.toAddSubgroup).mpr T.integralDual_positive_integral

end

namespace IntegralDualLe.Geometric.MarkedPolarizedTorus

end IntegralDualLe.Geometric.MarkedPolarizedTorus

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
