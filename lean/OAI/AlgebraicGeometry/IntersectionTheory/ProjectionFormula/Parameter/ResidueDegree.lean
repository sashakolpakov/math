import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationStalks

/-! # Residue Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ResidueDegree

noncomputable section

/-! The zero place has residue degree one over the ground field in the
native scheme pushforward, including the localization and residue maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

universe u

theorem residueDegree_over_field (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (a : PrimeSpectrum A) :
    (Spec.map (CommRingCat.ofHom (algebraMap k A))).residueDegree a =
      Module.finrank k a.asIdeal.ResidueField := by
  let p := a.asIdeal.under k
  let := Localization.AtPrime.algebraOfLiesOver p a.asIdeal
  rw [Affine.ResidueDegree.residueDegree_eq_inertiaDeg, Ideal.inertiaDeg_def]
  have he : Module.finrank k p.ResidueField = 1 := by
    rw [← (p.algEquivResidueFieldOfField).toLinearEquiv.finrank_eq, Module.finrank_self]
  have ht := Module.finrank_mul_finrank k p.ResidueField a.asIdeal.ResidueField
  simpa only [he, one_mul] using ht

theorem zero_place_residueDegree (k : Type u) [Field k] :
    (Spec.map (CommRingCat.ofHom (algebraMap k (ProjectionFormula.Polynomial.Place.localRing k)))).residueDegree
      (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing k)) = 1 := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k)))
  let f := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
  have hc : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (ProjectionFormula.Polynomial.Place.localRing k))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hp : j (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing k)) =
      (⟨ProjectionFormula.Polynomial.Place.zeroIdeal k, inferInstance⟩ : PrimeSpectrum (Polynomial k)) := by
    apply PrimeSpectrum.ext
    exact IsLocalization.AtPrime.under_maximalIdeal (ProjectionFormula.Polynomial.Place.localRing k) (ProjectionFormula.Polynomial.Place.zeroIdeal k)
  rw [← hc, CyclePushforward.residueDegree_comp, hp,
    LocalizationStalks.localization_residueDegree (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k)
      (ProjectionFormula.Polynomial.Place.zeroIdeal k).primeCompl, mul_one]
  exact (residueDegree_over_field k (Polynomial k) ⟨ProjectionFormula.Polynomial.Place.zeroIdeal k, inferInstance⟩).trans
    (ProjectionFormula.Polynomial.Place.residue_finrank k)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ResidueDegree
