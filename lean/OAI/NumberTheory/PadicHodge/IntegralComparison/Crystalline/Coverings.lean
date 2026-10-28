import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cartesian

/-! # Coverings -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Coverings

noncomputable section

/-!
# IntegralComparison: functoriality of crystalline covering families

The inclusion of the small site and postcomposition on the big site preserve
the actual covering families, including the cartesian closed subschemes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}

instance fromSmall_faithful :
    (BigCrystallineSite.fromSmall (p := p) (B := B) (J := J) (δ := δ) (f := f)).Faithful where
  map_injective h := Site.AffineThickening.Hom.ext _ _ (congrArg BigCrystallineSite.Object.Hom.ringMap h)

instance fromSmall_full :
    (BigCrystallineSite.fromSmall (p := p) (B := B) (J := J) (δ := δ) (f := f)).Full where
  map_surjective α := ⟨{ ringMap := α.ringMap, overBase := α.overBase, overX := α.overX }, rfl⟩

lemma fromSmall_ambient_presieve {U : Site.AffineThickening p B J δ f} (R : Presieve U) :
    (R.map BigCrystallineSite.fromSmall).map BigCrystallineSite.Object.ambient = R.map Site.AffineThickening.ambient := by
  obtain ⟨ι, V, α, rfl⟩ := R.exists_eq_ofArrows
  simp only [Presieve.map_ofArrows]
  rfl

lemma fromSmall_preserves_coverings :
    Site.AffineThickening.precoverage (p := p) (B := B) (J := J) (δB := δ) (f := f) ≤
      BigCrystallineSite.Object.precoverage.comap BigCrystallineSite.fromSmall := by
  intro U R hR
  change (R.map BigCrystallineSite.fromSmall).map BigCrystallineSite.Object.ambient ∈ Scheme.precoverage IsOpenImmersion _ ∧ _
  refine ⟨?_, ?_⟩
  · rw [fromSmall_ambient_presieve]
    exact hR
  · intro V α hα
    cases hα with
    | of hα =>
      have : IsOpenImmersion (Site.AffineThickening.ambient.map _) := hR.2 (Presieve.map.of hα)
      exact Cartesian.small_cover_cartesian _

variable {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of B)}
variable (g : X ⟶ Y) (hg : g ≫ fY = f)

instance postcompose_faithful :
    (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).Faithful where
  map_injective {U V} α β h := by
    have he := congrArg (fun t : (BigCrystallineSite.postcompose g hg).obj U ⟶ (BigCrystallineSite.postcompose g hg).obj V => t.ringMap) h
    exact BigCrystallineSite.Object.Hom.ext U V he

lemma postcompose_ambient_presieve {U : BigCrystallineSite.Object p B J δ f} (R : Presieve U) :
    (R.map (BigCrystallineSite.postcompose g hg)).map BigCrystallineSite.Object.ambient = R.map BigCrystallineSite.Object.ambient := by
  obtain ⟨ι, V, α, rfl⟩ := R.exists_eq_ofArrows
  simp only [Presieve.map_ofArrows]
  rfl

lemma postcompose_preserves_coverings :
    BigCrystallineSite.Object.precoverage (p := p) (J := J) (δ := δ) (f := f) ≤
      BigCrystallineSite.Object.precoverage.comap (BigCrystallineSite.postcompose g hg) := by
  intro U R hR
  refine ⟨?_, ?_⟩
  · rw [postcompose_ambient_presieve]
    exact hR.1
  · intro V α hα
    cases hα with
    | of hα => exact hR.2 _ hα

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Coverings
