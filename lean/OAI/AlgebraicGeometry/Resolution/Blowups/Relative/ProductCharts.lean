import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Product Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.ProductCharts.Construction

noncomputable section

/-! Actual base-change charts of a scheme-theoretic product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {P X S U : Scheme.{u}} (p : P ⟶ S) (f : X ⟶ S) (j : U ⟶ X)

def relativeProductChartMap : pullback p (j ≫ f) ⟶ pullback p f :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, pullback.condition])

theorem relativeProductChart_isPullback :
    IsPullback (relativeProductChartMap p f j) (pullback.snd p (j ≫ f))
      (pullback.snd p f) j := by
  have houter : IsPullback (relativeProductChartMap p f j ≫ pullback.fst p f)
      (pullback.snd p (j ≫ f)) p (j ≫ f) := by
    rw [relativeProductChartMap, pullback.lift_fst]
    exact IsPullback.of_hasPullback p (j ≫ f)
  exact houter.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p f)

instance relativeProductChartMap_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (relativeProductChartMap p f j) :=
  MorphismProperty.of_isPullback (relativeProductChart_isPullback p f j).flip inferInstance

theorem relativeProductChartMap_fst :
    relativeProductChartMap p f j ≫ pullback.fst p f = pullback.fst p (j ≫ f) :=
  pullback.lift_fst _ _ _

theorem relativeProductChartMap_snd :
    relativeProductChartMap p f j ≫ pullback.snd p f = pullback.snd p (j ≫ f) ≫ j :=
  pullback.lift_snd _ _ _

theorem pair_isClosedImmersion_iff_of_base_eq
    {B : Scheme.{u}} (q : B ⟶ P) (r : B ⟶ U) {g₁ g₂ : U ⟶ S} (hg : g₁ = g₂)
    (h₁ : q ≫ p = r ≫ g₁) (h₂ : q ≫ p = r ≫ g₂) :
    IsClosedImmersion (pullback.lift q r h₁) ↔ IsClosedImmersion (pullback.lift q r h₂) := by
  subst g₂
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.ProductCharts.Construction
