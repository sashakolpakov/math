import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IdealCartesianLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EqualizerIdealCriterion

/-! # Morphism Equality Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.MorphismEqualityLocus

noncomputable section

/-! Equality of two maps from a proper flat family is represented by an
actual closed base locus, with its universal property on all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem equalizerIdeal_baseChange_zero_iff
    {S T : Scheme.{u}} {X Y : Over S} [IsSeparated Y.hom]
    (b : T ⟶ S) (f g : X ⟶ Y) :
    (equalizer.ι f g).left.ker.comap (pullback.fst X.hom b) = ⊥ ↔
      (Over.pullback b).map f = (Over.pullback b).map g := by
  let c : (Over.map b).obj ((Over.pullback b).obj X) ⟶ X :=
    Over.homMk (pullback.fst X.hom b) pullback.condition
  constructor
  · intro h
    have hc : c ≫ f = c ≫ g :=
      (HilbertScheme.Presentations.EqualizerIdealCriterion.equalizer_ideal_comap_eq_bot_iff f g c).mp h
    have he := congrArg Over.Hom.left hc
    change pullback.fst X.hom b ≫ f.left = pullback.fst X.hom b ≫ g.left at he
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.pullback_map_left, pullback.lift_fst] using he
    · simp only [Over.pullback_map_left, pullback.lift_snd]
  · intro h
    apply (HilbertScheme.Presentations.EqualizerIdealCriterion.equalizer_ideal_comap_eq_bot_iff f g c).mpr
    apply Over.OverMorphism.ext
    change pullback.fst X.hom b ≫ f.left = pullback.fst X.hom b ≫ g.left
    have he := congrArg
      (fun z : (Over.pullback b).obj X ⟶ (Over.pullback b).obj Y =>
        z.left ≫ pullback.fst Y.hom b) h
    simpa only [Over.pullback_map_left, pullback.lift_fst] using he

theorem proper_flat_morphism_equality_closed_locus
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : Over S}
    [IsProper X.hom] [Flat X.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk (𝟙 S)), IsClosedImmersion j.left ∧
      ∀ T : Over S,
        (Over.pullback T.hom).map f = (Over.pullback T.hom).map g ↔
          ∃! y : T ⟶ Z, y ≫ j = Over.mkIdTerminal.from T := by
  obtain ⟨Z, j, hj, ht⟩ := Proper.IdealCartesianLocus.proper_ideal_baseChange_closed_locus X (equalizer.ι f g).left.ker
  exact ⟨Z, j, hj, fun T =>
    (equalizerIdeal_baseChange_zero_iff T.hom f g).symm.trans (ht T)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.MorphismEqualityLocus
