import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ResidueDegree
import Mathlib.RingTheory.Ideal.Height

/-! # Localization Stalks -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationStalks

noncomputable section

/-! Localization preserves the actual scheme stalks, residue degrees, and
codimensions at its source points. These comparisons connect the global
normalization charts with the normalization of a local ring. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]

include M

theorem localRingHom_bijective (q : PrimeSpectrum S) :
    Function.Bijective (Localization.localRingHom (q.asIdeal.under R) q.asIdeal
      (algebraMap R S) rfl) := by
  let A := Localization.AtPrime (q.asIdeal.under R)
  let B := Localization.AtPrime q.asIdeal
  let : IsLocalization.AtPrime B (q.asIdeal.under R) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M B q.asIdeal
  let e : A ≃ₐ[R] B := IsLocalization.algEquiv (q.asIdeal.under R).primeCompl A B
  have he : Localization.localRingHom (q.asIdeal.under R) q.asIdeal
      (algebraMap R S) rfl = e.toRingHom := by
    apply IsLocalization.ringHom_ext (q.asIdeal.under R).primeCompl
    ext r
    change Localization.localRingHom _ _ _ rfl (algebraMap R A r) = e (algebraMap R A r)
    rw [Localization.localRingHom_to_map, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  rw [he]
  exact e.bijective

theorem localization_stalkMap_isIso (q : Spec (.of S)) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q) := by
  rw [← Scheme.localRingHom_comp_stalkIso]
  let : IsIso (CommRingCat.ofHom (Localization.localRingHom
      (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (localRingHom_bijective R S M q)
  change IsIso ((Spec.stalkIso (.of R) ⟨q.asIdeal.under R, inferInstance⟩).hom ≫
    CommRingCat.ofHom (Localization.localRingHom (q.asIdeal.under R) q.asIdeal
      (algebraMap R S) rfl) ≫ (Spec.stalkIso (.of S) q).inv)
  infer_instance

theorem localization_residueDegree (q : Spec (.of S)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).residueDegree q = 1 := by
  let := localization_stalkMap_isIso R S M q
  exact Stalk.ResidueDegree.residueDegree_of_isIso_stalkMap _ _

theorem localization_coheight (q : Spec (.of S)) :
    Order.coheight ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q) =
      Order.coheight q := by
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact IsLocalization.height_under M q.asIdeal

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationStalks
