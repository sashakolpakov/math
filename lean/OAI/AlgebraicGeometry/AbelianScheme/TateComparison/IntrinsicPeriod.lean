import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PeriodCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps

/-! # Intrinsic Period -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPeriod

noncomputable section

/-! The natural completed-period comparison for actual native complex
abelian varieties and their algebraic group morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps

variable (q : ℕ) [Fact q.Prime]

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
  HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A

def nativeCompletedPeriodTateEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ℤ_[q] ⊗[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A ≃ₗ[ℤ_[q]]
      Add.schemeTateModule A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q :=
  (PeriodCoordinates.completedPeriodTateEquiv q (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A)).trans
    (TateProducts.Tate.mapEquiv q (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A))

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f]

def nativePeriodLatticeMap : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A →ₗ[ℤ] HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B :=
  PeriodNaturality.periodLatticeMap (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
    ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℚ) (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_preserves f)

omit [Fact q.Prime] in
theorem nativePeriodDivision_natural (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (n : ℕ) :
    (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A (PeriodMap.periodDivisionPoint q (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) n x)).toMul ≫ f =
      (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv B (PeriodMap.periodDivisionPoint q (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) n (nativePeriodLatticeMap f x))).toMul := by
  have hh := AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_period f (((q : ℚ) ^ n)⁻¹ • x.val)
  have hs := ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℚ).map_smul (((q : ℚ) ^ n)⁻¹) x.val
  change AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f (((q : ℚ) ^ n)⁻¹ • x.val) = ((q : ℚ) ^ n)⁻¹ • AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f x.val at hs
  rw [hs] at hh
  exact hh

theorem nativePeriodTateMap_natural (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    Add.schemeTateMap A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q f
        (Add.Tate.map q (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).toAddMonoidHom (PeriodMap.periodTateMap q (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) x)) =
      Add.Tate.map q (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv B).toAddMonoidHom
        (PeriodMap.periodTateMap q (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) (nativePeriodLatticeMap f x)) := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact congrArg Additive.ofMul (nativePeriodDivision_natural q f x n)

theorem nativeCompletedPeriodTateEquiv_tmul (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (z : ℤ_[q])
    (x : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    nativeCompletedPeriodTateEquiv q A (z ⊗ₜ[ℤ] x) =
      z • Add.Tate.map q (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).toAddMonoidHom (PeriodMap.periodTateMap q (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) x) := by
  change Add.Tate.map q (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).toAddMonoidHom
    (PeriodNaturality.completedPeriodTateMap q (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (z ⊗ₜ[ℤ] x)) = _
  rw [PeriodNaturality.completedPeriodTateMap_tmul]
  exact (Add.Tate.map q (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).toAddMonoidHom).map_smul z (PeriodMap.periodTateMap q (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) x)

theorem nativeCompletedPeriodTate_natural :
    (Add.schemeTateMap A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q f).comp
        (nativeCompletedPeriodTateEquiv q A).toLinearMap =
      (nativeCompletedPeriodTateEquiv q B).toLinearMap.comp
        ((nativePeriodLatticeMap f).baseChange ℤ_[q]) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, nativeCompletedPeriodTateEquiv_tmul,
      LinearMap.baseChange_tmul, map_smul, nativePeriodTateMap_natural]
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPeriod
