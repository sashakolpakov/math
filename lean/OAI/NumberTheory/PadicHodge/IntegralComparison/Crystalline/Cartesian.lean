import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Cartesian -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cartesian

noncomputable section

/-!
# IntegralComparison: cartesian coverings in the crystalline sites

For the small crystalline site, a morphism which is an open immersion on
ambient thickenings is automatically cartesian on the closed subschemes.
This verifies the compatibility of the existing small-site coverings with
the explicit covering condition in the big site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

lemma isPullback_of_open_closed_surjective {U V T S : Scheme.{u}}
    (a : U ⟶ V) (i : U ⟶ T) (j : V ⟶ S) (b : T ⟶ S)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsClosedImmersion j]
    (h : a ≫ j = i ≫ b) (hi : Function.Surjective i) : IsPullback a i j b := by
  let l : U ⟶ pullback j b := pullback.lift a i h
  have hfst : l ≫ pullback.fst j b = a := pullback.lift_fst _ _ _
  have hsnd : l ≫ pullback.snd j b = i := pullback.lift_snd _ _ _
  have : IsOpenImmersion (l ≫ pullback.fst j b) := by rw [hfst]; infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (pullback.fst j b)
  have hsurj : Function.Surjective l := by
    intro z
    obtain ⟨x, hx⟩ := hi (pullback.snd j b z)
    refine ⟨x, ?_⟩
    apply (pullback.snd j b).isClosedEmbedding.injective
    change (l ≫ pullback.snd j b) x = pullback.snd j b z
    rw [hsnd]
    exact hx
  have : Epi l.base := (TopCat.epi_iff_surjective l.base).mpr hsurj
  have : IsIso l := IsOpenImmersion.isIso l
  exact IsPullback.of_iso_pullback ⟨h⟩ (asIso l) hfst hsnd

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V : Site.AffineThickening p B J δ f} (α : U ⟶ V)

lemma small_cover_cartesian [IsOpenImmersion (Site.AffineThickening.ambient.map α)] :
    BigCrystallineSite.Object.Cartesian
      (BigCrystallineSite.fromSmall.map α) := by
  let a := Spec.map (CommRingCat.ofHom (Site.AffineThickening.quotientMap U V α.ringMap))
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk U.ideal))
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk V.ideal))
  let b := Spec.map (CommRingCat.ofHom α.ringMap.toRingHom)
  have ha : IsOpenImmersion a := by
    have : IsOpenImmersion (a ≫ V.openMap) := by
      change IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (Site.AffineThickening.quotientMap U V α.ringMap)) ≫ V.openMap)
      rw [α.overX]
      infer_instance
    exact IsOpenImmersion.of_comp a V.openMap
  have hb : IsOpenImmersion b := inferInstanceAs (IsOpenImmersion (Site.AffineThickening.ambient.map α))
  have hj : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hi : Function.Surjective i := by
    apply (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical (I := U.ideal) ?_).2
    intro x hx
    exact mem_nilradical.mpr (U.nilIdeal x hx)
  have h : a ≫ j = i ≫ b := by
    change Spec.map (CommRingCat.ofHom (Site.AffineThickening.quotientMap U V α.ringMap)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk V.ideal)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk U.ideal)) ≫ Spec.map (CommRingCat.ofHom α.ringMap.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  exact isPullback_of_open_closed_surjective a i j b h hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cartesian
