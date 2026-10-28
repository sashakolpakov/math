import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedRelations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced

/-! # Represented Relations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentedRelations

noncomputable section

/-! A represented relation with reduced source and finite etale source
projection is an internal equivalence relation once its reduced-test
points form equivalence relations and the two maps are jointly monic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_equivalenceRelation_of_reduced_hom {S : Scheme.{0}}
    {R X : Over S} (s t : R ⟶ X) [IsReduced X.left] [IsReduced R.left]
    [IsFinite s.left] [Etale s.left] [JointlyMono₂ s t]
    (he : ∀ (T : Over S) [IsReduced T.left], Equivalence (AbelianModuli.ReferenceFamily.RepresentedRelations.homRelation s t (T := T))) :
    Nonempty (CategoryTheory.EquivalenceRelation s t) := by
  have hsq := (IsPullback.of_hasPullback t s).map (Over.forget S)
  have : IsFinite (pullback.fst t s).left :=
    MorphismProperty.of_isPullback hsq.flip (inferInstanceAs (IsFinite s.left))
  have : Etale (pullback.fst t s).left :=
    MorphismProperty.of_isPullback hsq.flip (inferInstanceAs (Etale s.left))
  have : IsReduced (pullback t s).left := Finite.EtaleReduced.finite_etale_isReduced (pullback.fst t s).left
  obtain ⟨r, hrs, hrt⟩ := (he X).refl (𝟙 X)
  obtain ⟨u, hus, hut⟩ := (he R).symm
    (show AbelianModuli.ReferenceFamily.RepresentedRelations.homRelation s t s t from ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩)
  have hpair : AbelianModuli.ReferenceFamily.RepresentedRelations.homRelation s t (pullback.fst t s ≫ s) (pullback.snd t s ≫ t) :=
    (he (pullback t s)).trans ⟨pullback.fst t s, rfl, pullback.condition⟩
      ⟨pullback.snd t s, rfl, rfl⟩
  obtain ⟨v, hvs, hvt⟩ := hpair
  exact ⟨{
    r := r
    reflexivity₁ := hrs
    reflexivity₂ := hrt
    s := u
    symmetry₁ := hus
    symmetry₂ := hut
    c := pullback.cone t s
    isLimit := pullback.isLimit t s
    t := v
    transitivity₁ := hvs
    transitivity₂ := hvt }⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentedRelations
