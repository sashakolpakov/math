import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.RestrictedResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafComplex

/-! # Open Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenResolution.AffineOpenResolution

noncomputable section

/-! Sections of an actual native-form injective resolution are exact on every rational affine open. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Algebra ℚ R] (X : Over (Spec (CommRingCat.of R)))

def openModel (W : X.left.Opens) : Over (Spec (CommRingCat.of R)) := Over.mk (W.ι ≫ X.hom)

def inclusion (W : X.left.Opens) : openModel R X W ⟶ X := Over.homMk W.ι

omit [Algebra ℚ R] in
theorem image_top (W : X.left.Opens) : W.ι ''ᵁ ⊤ = W := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

theorem forms_exactAt (j : ℕ) (I : InjectiveResolution ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j))
    (W : X.left.Opens) (hW : IsAffineOpen W) (n : ℕ) :
    (((OpenSheafComplex.OpenSheafSectionComplex.sections R X.left W).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).ExactAt (n + 1) := by
  have : IsAffine (openModel R X W).left := hW
  have : IsOpenImmersion (inclusion R X W).left := inferInstanceAs (IsOpenImmersion W.ι)
  exact (RestrictedResolution.AffineRestrictedResolution.forms_exact_succ R (inclusion R X W) j I n).of_iso
    (OpenSheafComplex.OpenSheafSectionComplex.complexIso R W.ι W (image_top R X W) I.cocomplex)

theorem forms_sections_exact (j : ℕ)
    (I : InjectiveResolution ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j))
    (W : X.left.Opens) (hW : IsAffineOpen W) (n : ℕ)
    (x : (I.cocomplex.X (n + 1)).obj.obj (op W))
    (hx : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op W) x = 0) :
    ∃ y : (I.cocomplex.X n).obj.obj (op W),
      (I.cocomplex.d n (n + 1)).hom.app (op W) y = x := by
  have h := forms_exactAt R X j I W hW n
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at h
  exact (ShortComplex.moduleCat_exact_iff _).mp h x hx

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenResolution.AffineOpenResolution
