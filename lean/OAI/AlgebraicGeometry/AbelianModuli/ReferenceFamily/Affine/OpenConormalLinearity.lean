import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenConormalCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CoefficientConormalLinearity

/-! # Open Conormal Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenConormalLinearity

noncomputable section

/-! On every actual affine open of a smooth integral complex group,
the constructed conormal coordinates are linear over the section ring.
The empty affine open is included. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine Y.left] (i : Y ⟶ A) [IsOpenImmersion i.left]

include i in
omit [IsIntegral A.left] [GrpObj A] in
theorem affineOpenAlgebra_smooth : Algebra.Smooth ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y) := by
  have : Smooth (i.left ≫ A.hom) := inferInstance
  have : Smooth Y.hom := (congrArg Smooth i.w).mp this
  exact HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth ℂ Y

include i in
omit [Smooth A.hom] [GrpObj A] in
theorem affineOpenAlgebra_isDomain [Nontrivial (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y)] :
    IsDomain (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y) := by
  have : Nonempty Y.left := Nonempty.map (OpenConormalCoordinates.affineOpenCoordinateIso ℂ Y).inv.left
    (inferInstanceAs (Nonempty (PrimeSpectrum (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y))))
  have : IsIntegral Y.left := isIntegral_of_isOpenImmersion i.left
  exact inferInstanceAs (IsDomain Γ(Y.left, ⊤))

def affineOpenConormalLinearEquiv :
    Derivation ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y) ≃ₗ[HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y]
      (Constructed.IdentityConormal.constructedIdentityConormal ℂ A →ₗ[ℂ] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y) := by
  let B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y
  let F := OpenConormalCoordinates.affineOpenConormalEquiv ℂ A Y i
  refine { toEquiv := F, map_add' := ?_, map_smul' := ?_ }
  · intro d e
    cases subsingleton_or_nontrivial B with
    | inl h =>
      let := h
      exact Subsingleton.elim _ _
    | inr h =>
      let := h
      have : Algebra.Smooth ℂ B := affineOpenAlgebra_smooth A Y i
      have : IsDomain B := affineOpenAlgebra_isDomain A Y i
      exact Regular.CoefficientConormalLinearity.regularCoefficientConormal_add A B (OpenConormalCoordinates.affineOpenCoordinateInclusion ℂ A Y i) B d e
  · intro c d
    cases subsingleton_or_nontrivial B with
    | inl h =>
      let := h
      exact Subsingleton.elim _ _
    | inr h =>
      let := h
      have : Algebra.Smooth ℂ B := affineOpenAlgebra_smooth A Y i
      have : IsDomain B := affineOpenAlgebra_isDomain A Y i
      exact Regular.CoefficientConormalLinearity.regularCoefficientConormal_smul A B (OpenConormalCoordinates.affineOpenCoordinateInclusion ℂ A Y i) B c d

theorem affineOpenConormalLinearEquiv_apply
    (d : Derivation ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ Y)) :
    affineOpenConormalLinearEquiv A Y i d = OpenConormalCoordinates.affineOpenConormalEquiv ℂ A Y i d := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenConormalLinearity
