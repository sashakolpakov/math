import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Changed Open Chart Smooth -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedOpenChartSmooth

noncomputable section

/-! Open charts of an ambient scheme become smooth when the recovered ambient scheme is smooth. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem baseChangedOpenChart_smooth
    {S T : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) [IsOpenImmersion j.left]
    (c : T ⟶ S) [Smooth ((Over.pullback c).obj Y).hom] :
    Smooth ((Over.pullback c).obj X).hom := by
  let j' := (Over.pullback c).map j
  have : IsOpenImmersion j'.left := MorphismProperty.of_isPullback (Projective.PresentationBaseChange.overPullback_map_isPullback j c) inferInstance
  have hs : Smooth (j'.left ≫ ((Over.pullback c).obj Y).hom) := inferInstance
  exact (congrArg Smooth j'.w).mp hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedOpenChartSmooth
