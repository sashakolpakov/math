import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Circle
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Intrinsic Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicBasis

noncomputable section

/-! Integral and rational Tate bases of an actual complex abelian variety,
constructed from its proved period lattice and circle torsion coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (q : ℕ) [Fact q.Prime]

local instance : IsIntegral A.toOver.left := A.variety.property
local instance : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance : ConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.native_connectedSpace AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A
local instance : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A

abbrev nativeTateRank := 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom

def nativePeriodCircleEquiv :
    (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ⧸ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A).toAddSubgroup) ≃+
      (Fin (nativeTateRank A) → UnitAddCircle) := by
  let b := AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A
  let B := b.ofZLatticeBasis ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
  exact (QuotientAddGroup.quotientAddEquivOfEq
    (congrArg Submodule.toAddSubgroup (b.ofZLatticeBasis_span ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)))).symm.trans
      (AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.basisTorusEquiv B)

def nativeTateEquiv :
    Add.schemeTateModule A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q ≃ₗ[ℤ_[q]]
      (Fin (nativeTateRank A) → ℤ_[q]) :=
  (TateProducts.Tate.mapEquiv q (AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.nativePeriodAddEquiv A).symm).trans
    ((TateProducts.Tate.mapEquiv q (nativePeriodCircleEquiv A)).trans
      ((TateProducts.Tate.piEquiv q (fun _ : Fin (nativeTateRank A) => UnitAddCircle)).trans
        (LinearEquiv.piCongrRight fun _ => (Circle.circleTateEquiv q).symm)))

def nativeTateBasis : Module.Basis (Fin (nativeTateRank A)) ℤ_[q]
    (Add.schemeTateModule A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) :=
  (Pi.basisFun ℤ_[q] (Fin (nativeTateRank A))).map (nativeTateEquiv A q).symm

def nativeRationalTateBasis : Module.Basis (Fin (nativeTateRank A)) ℚ_[q]
    (Rational.rationalTateModule A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) :=
  (nativeTateBasis A q).baseChange ℚ_[q]

theorem nativeTate_finrank :
    Module.finrank ℤ_[q] (Add.schemeTateModule A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) = nativeTateRank A := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (nativeTateBasis A q)

theorem nativeRationalTate_finrank :
    Module.finrank ℚ_[q] (Rational.rationalTateModule A.toOver (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) = nativeTateRank A := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (nativeRationalTateBasis A q)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicBasis
