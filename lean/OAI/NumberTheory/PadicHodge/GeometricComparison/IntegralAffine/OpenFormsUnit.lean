import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FormsOpenUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FirstThreeUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenResolution

/-! # Open Forms Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.OpenFormsUnit.IntegralAffineOpenFormsUnit

noncomputable section

/-! The actual native form-presheaf sheafification unit is invertible on every affine open through degree two over any base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

theorem top [IsAffine X.left] (n : ℕ) (hn : n ≤ 2) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op ⊤)) := by
  let : Algebra R Γ(X.left, ⊤) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X ⊤
  let f := (Affine.OverSpec.AffineOverSpec.iso R X).inv
  have : IsIso f.left := (Over.forget _).map_isIso f
  have : IsOpenImmersion f.left := inferInstance
  have h := Intrinsic.FormsOpenUnit.IntrinsicFormsOpenUnit.isIso_on_image R f n ⊤
    (FirstThreeUnit.IntegralAffineFirstThreeSheaf.unit_top_isIso R Γ(X.left, ⊤) n hn)
  have hf : f.left ''ᵁ ⊤ = ⊤ :=
    (Scheme.Hom.image_top_eq_opensRange f.left).trans (Scheme.Hom.opensRange_of_isIso f.left)
  exact hf ▸ h

theorem on_open (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) (hn : n ≤ 2) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op U)) := by
  have : IsAffine (Affine.OpenResolution.AffineOpenResolution.openModel R X U).left := hU
  have : IsOpenImmersion (Affine.OpenResolution.AffineOpenResolution.inclusion R X U).left :=
    inferInstanceAs (IsOpenImmersion U.ι)
  have h := Intrinsic.FormsOpenUnit.IntrinsicFormsOpenUnit.isIso_on_image R (Affine.OpenResolution.AffineOpenResolution.inclusion R X U) n ⊤
    (top R (Affine.OpenResolution.AffineOpenResolution.openModel R X U) n hn)
  exact (Affine.OpenResolution.AffineOpenResolution.image_top R X U) ▸ h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.OpenFormsUnit.IntegralAffineOpenFormsUnit
