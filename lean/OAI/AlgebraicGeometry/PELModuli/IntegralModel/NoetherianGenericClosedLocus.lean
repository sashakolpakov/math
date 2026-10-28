import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianVerticalImage
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseFunctorRepresentation
import OAI.AlgebraicGeometry.Albanese.Construction.ReducedFactor

/-! # Noetherian Generic Closed Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianGenericClosedLocus

noncomputable section

/-! A closed condition holding on the generic fiber holds uniformly
after localization on a reduced noetherian parameter scheme. The resulting
factorization persists on arbitrary tests, including nonreduced tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem noetherian_generic_closed_locus_away
    {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (.of R)) (C : Set X) (hC : IsClosed C)
    (hgeneric : ∀ x : X, (p x).asIdeal = ⊥ → x ∈ C) :
    ∃ r : R, r ≠ 0 ∧ ∀ x : X, r ∉ (p x).asIdeal → x ∈ C := by
  let U : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace U.ι
  have : IsNoetherian U.toScheme := ⟨⟩
  obtain ⟨r, hr, hu⟩ := NoetherianVerticalImage.noetherian_vertical_image_annihilator (U.ι ≫ p)
    (fun x hx => x.property (hgeneric x.val hx))
  refine ⟨r, hr, fun x hx => ?_⟩
  by_contra hn
  exact hx (hu (⟨x, hn⟩ : U.toScheme))

theorem noetherian_generic_closed_factorization_away
    {R : Type} [CommRing R] [IsDomain R] {X Y : Scheme.{0}}
    [IsNoetherian X] [IsReduced X] (p : X ⟶ Spec (.of R))
    (i : Y ⟶ X) [IsClosedImmersion i]
    (hgeneric : ∀ x : X, (p x).asIdeal = ⊥ → x ∈ Set.range i) :
    ∃ r : R, r ≠ 0 ∧ ∀ {T : Scheme.{0}} (t : T ⟶ X),
      (∀ x : T, r ∉ (p (t x)).asIdeal) → ∃! q : T ⟶ Y, q ≫ i = t := by
  obtain ⟨r, hr, hs⟩ := noetherian_generic_closed_locus_away p (Set.range i)
    i.isClosedEmbedding.isClosed_range hgeneric
  let U : X.Opens := p ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have hU : Set.range U.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    exact fun x hx => hs x hx
  let u := Albanese.Construction.ReducedFactor.factorThroughClosed i U.ι hU
  have hu : u ≫ i = U.ι := Albanese.Construction.ReducedFactor.factorThroughClosed_comp i U.ι hU
  refine ⟨r, hr, fun t ht => ?_⟩
  let a := Open.BaseFunctorRepresentation.OpenBaseTest.lift U (Over.mk t) ht
  have ha : a ≫ U.ι = t := Open.BaseFunctorRepresentation.OpenBaseTest.lift_ι U (Over.mk t) ht
  have hq : (a ≫ u) ≫ i = t := (Category.assoc _ _ _).trans
    ((congrArg (a ≫ ·) hu).trans ha)
  exact ⟨a ≫ u, hq, fun q h => (cancel_mono i).mp (h.trans hq.symm)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NoetherianGenericClosedLocus
