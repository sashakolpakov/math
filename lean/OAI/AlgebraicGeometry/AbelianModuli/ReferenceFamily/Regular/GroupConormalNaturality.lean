import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupConormalLiftNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCoefficientSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.CoefficientDetection

/-! # Group Conormal Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.GroupConormalNaturality

noncomputable section

/-! Conormal pullback commutes with the actual group-lift coordinates
over every reduced finite-type complex coefficient algebra. Actual
complex characters detect the equality, using the proved coefficient
squares and the native differential comparison at each character. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    [IsIntegral B.left] [Smooth B.hom] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (C : Type) [CommRing C] [Algebra ℂ C]
    (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A)

def coefficientGroupPostcomposeLift
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ c}) :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ B // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ (c ≫ f)} :=
  ⟨u.val ≫ f, by rw [← Category.assoc, u.property, Category.assoc]⟩

variable [Algebra.FiniteType ℂ C] [IsReduced C]

theorem regularGroupConormal_natural
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ c}) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ B C (c ≫ f) (coefficientGroupPostcomposeLift f C c u) =
      (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C c u).comp (Intrinsic.GroupConormalMap.constructedConormalPullback f) := by
  apply LinearMap.ext
  intro z
  apply Complex.CoefficientDetection.complexCoefficientCharacters_ext C
  intro q
  let t := Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber C) (DualNumber ℂ) (Dual.NumberCoefficients.dualNumberAlgMap q)
  let cq := t ≫ c
  let uq := Constructed.IdentityConormalNaturality.constructedIdentityRestrictedLift ℂ A C ℂ q c u
  have hA := Constructed.IdentityConormalNaturality.constructedIdentityLiftConormalEquiv_natural ℂ A C ℂ q c u (Intrinsic.GroupConormalMap.constructedConormalPullback f z)
  have hc : t ≫ (c ≫ f) = cq ≫ f := (Category.assoc _ _ _).symm
  have hu : t ≫ (coefficientGroupPostcomposeLift f C c u).val =
      (Intrinsic.GroupConormalLiftNaturality.groupConormalPostcomposeLift f cq uq).val := (Category.assoc _ _ _).symm
  have hB := Constructed.ConormalCoefficientSquare.constructedIdentityLiftConormalEquiv_square ℂ B C ℂ q (c ≫ f) (cq ≫ f)
    (coefficientGroupPostcomposeLift f C c u) (Intrinsic.GroupConormalLiftNaturality.groupConormalPostcomposeLift f cq uq) hc hu z
  have hp := LinearMap.congr_fun (Intrinsic.GroupConormalLiftNaturality.constructedConormalPullback_coordinates f cq uq) z
  exact hB.symm.trans (hp.trans hA)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.GroupConormalNaturality
