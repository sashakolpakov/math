import Mathlib.AlgebraicGeometry.PullbackCarrier
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianVerticalImage
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Generic Open Equality Localization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericOpenEqualityLocalization

noncomputable section

/-! Equal generic opens agree after one coefficient localization.
The generic condition can be verified on an actual field base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem noetherian_generic_open_inclusion_away
    {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (.of R)) (U V : X.Opens)
    (hgeneric : ∀ x : X, (p x).asIdeal = ⊥ → x ∈ U → x ∈ V) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : X, r ∉ (p x).asIdeal → x ∈ U → x ∈ V := by
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace U.ι
  have : IsNoetherian U.toScheme := ⟨⟩
  obtain ⟨r, hr, h⟩ := NoetherianVerticalImage.noetherian_generic_open_locus_away (U.ι ≫ p) (U.ι ⁻¹ᵁ V)
    (fun x hx => hgeneric x.val hx x.property)
  exact ⟨r, hr, fun x hx hu => h ⟨x, hu⟩ hx⟩

theorem noetherian_generic_open_equality_away
    {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (.of R)) (U V : X.Opens)
    (hgeneric : ∀ x : X, (p x).asIdeal = ⊥ → (x ∈ U ↔ x ∈ V)) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : X, r ∉ (p x).asIdeal → (x ∈ U ↔ x ∈ V) := by
  obtain ⟨r, hr, hUV⟩ := noetherian_generic_open_inclusion_away p U V
    (fun x hx => (hgeneric x hx).mp)
  obtain ⟨s, hs, hVU⟩ := noetherian_generic_open_inclusion_away p V U
    (fun x hx => (hgeneric x hx).mpr)
  refine ⟨r * s, mul_ne_zero hr hs, fun x hx => ⟨hUV x ?_, hVU x ?_⟩⟩
  · exact fun h => hx ((p x).asIdeal.mul_mem_right s h)
  · exact fun h => hx ((p x).asIdeal.mul_mem_left r h)

theorem generic_open_equality_away_of_field_baseChange
    {R K : Type} [CommRing R] [IsDomain R] [Field K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {X : Scheme.{0}} [IsNoetherian X] (p : X ⟶ Spec (.of R)) (U V : X.Opens)
    (h : pullback.fst p (Spec.map (CommRingCat.ofHom ι)) ⁻¹ᵁ U =
      pullback.fst p (Spec.map (CommRingCat.ofHom ι)) ⁻¹ᵁ V) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : X, r ∉ (p x).asIdeal → (x ∈ U ↔ x ∈ V) := by
  apply noetherian_generic_open_equality_away p U V
  intro x hx
  let b := Spec.map (CommRingCat.ofHom ι)
  have hb : p x ∈ Set.range b := by
    refine ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    exact (Ideal.comap_bot_of_injective ι hι).trans hx.symm
  have hlift : x ∈ Set.range (pullback.fst p b) := by
    rw [Scheme.Pullback.range_fst]
    exact hb
  obtain ⟨y, rfl⟩ := hlift
  exact Iff.of_eq (congrArg (fun W => y ∈ W) h)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericOpenEqualityLocalization
