import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalPullback

/-! # Covers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Covers

noncomputable section

/-!
# IntegralComparison: principal crystalline coverings and base change

Functions generating the unit ideal give a genuine covering family of
principal crystalline localizations. Pulling it back gives the covering
by the images of those functions, with the previously proved pullbacks.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable (U : BigCrystallineSite.Object p B J δ f) {ι : Type v} (r : ι → U.ring)

def presieve : Presieve U := Presieve.ofArrows (fun i => Crystalline.Localization.object U (r i)) (fun i => Crystalline.Localization.hom U (r i))

lemma covering (hr : Ideal.span (Set.range r) = ⊤) : presieve U r ∈ BigCrystallineSite.Object.precoverage U := by
  constructor
  · change (Presieve.ofArrows _ _).map BigCrystallineSite.Object.ambient ∈ Scheme.precoverage IsOpenImmersion _
    rw [Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun i => inferInstance⟩
    intro x
    have hex : ∃ i, r i ∉ x.asIdeal := by
      by_contra! h
      have hs : Ideal.span (Set.range r) ≤ x.asIdeal := Ideal.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact h i)
      rw [hr, top_le_iff] at hs
      exact x.isPrime.ne_top hs
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    change x ∈ (BigCrystallineSite.Object.ambient.map (Crystalline.Localization.hom U (r i))).opensRange
    rw [Crystalline.Localization.hom_range]
    exact hi
  · intro V α hα
    cases hα with
    | mk i => exact Crystalline.Localization.hom_cartesian U (r i)

lemma coveringSieve (hr : Ideal.span (Set.range r) = ⊤) :
    Sieve.generate (presieve U r) ∈ BigCrystallineSite.Object.topology U :=
  BigCrystallineSite.Object.precoverage.generate_mem_toGrothendieck (covering U r hr)

variable {U} {V : BigCrystallineSite.Object p B J δ f} (α : V ⟶ U)

lemma image_generates (hr : Ideal.span (Set.range r) = ⊤) :
    Ideal.span (Set.range (fun i => α.ringMap (r i))) = ⊤ := by
  have h := congrArg (Ideal.map α.ringMap.toRingHom) hr
  rw [Ideal.map_span, ← Set.range_comp, Ideal.map_top] at h
  exact h

lemma basechange_covering (hr : Ideal.span (Set.range r) = ⊤) :
    presieve V (fun i => α.ringMap (r i)) ∈ BigCrystallineSite.Object.precoverage V :=
  covering V _ (image_generates r α hr)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Covers
