import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ScalarPullback
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Univariate Scalar Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnivariateScalarPullback

noncomputable section

/-! The ordinary univariate polynomial coefficient square is an
actual scheme pullback, with its specified native coordinate maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

theorem naturality : (MvPolynomial.uniqueAlgEquiv S Unit).toRingHom.comp (MvPolynomial.map f) =
    (Polynomial.mapRingHom f).comp (MvPolynomial.uniqueAlgEquiv R Unit).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    simp

def iso (R : Type) [CommRing R] : Spec (.of R[X]) ≅ Spec (.of (MvPolynomial Unit R)) :=
  Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv R Unit).toRingEquiv.toCommRingCatIso.op

theorem iso_base (R : Type) [CommRing R] :
    (iso R).hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial Unit R)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])) := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R Unit).toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (MvPolynomial.uniqueAlgEquiv R Unit).commutes r

theorem isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : S →+* S[X])))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom f)) := by
  apply (ProjectionFormula.Polynomial.ScalarPullback.isPullback f Unit).of_iso'
    (iso S) (iso R) (Iso.refl _) (Iso.refl _)
  · change Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv S Unit).toRingHom) ≫ _ =
      _ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv R Unit).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (naturality f)
  · simpa only [Iso.refl_hom, Category.comp_id] using iso_base S
  · simpa only [Iso.refl_hom, Category.comp_id] using iso_base R
  · simp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnivariateScalarPullback
