import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftCharts

/-! # Lift Chart Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftChartSquare

noncomputable section

/-! Each constructed standard-etale chart has the original source
chart as its exact Cartesian reduction over the original target. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace Charts
universe u
variable {X X₀ Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
  (f : Y₀ ⟶ X₀) [Etale f] [IsAffineHom f]

theorem chart_square (a : LiftCharts.Index i f) :
    IsPullback (LiftCharts.reduction i f a) (LiftCharts.sourceMap i f a ≫ f) (LiftCharts.chartMap i f a) i := by
  have hs : IsPullback (Spec.map (i ∣_ a.1.1).appTop)
      (i ⁻¹ᵁ a.1.1).toScheme.isoSpec.inv a.1.1.toScheme.isoSpec.inv (i ∣_ a.1.1) :=
    IsPullback.of_vert_isIso ⟨Scheme.isoSpec_inv_naturality (i ∣_ a.1.1)⟩
  have h := ((Finite.StandardEtaleLift.square (LiftCharts.thickRing a.1) (LiftCharts.residueRing i a.1)
    (LiftCharts.coefficient_surjective i a.1) (LiftCharts.pair i f a)).paste_vert hs).paste_vert
      (isPullback_morphismRestrict i a.1.1)
  have he := Relative.StandardEtaleCover.presentedMap_over f (LiftCharts.baseCover i) a
  dsimp only [LiftCharts.pair, Relative.StandardEtaleCover.baseRing, LiftCharts.baseCover, LiftCharts.residueRing,
    LiftCharts.sourceMap, LiftCharts.reducedChart] at he
  dsimp only [LiftCharts.chartMap, LiftCharts.chartBase, LiftCharts.reduction, LiftCharts.sourceMap]
  rw [he]
  simpa only [Category.assoc] using h

end Charts

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftChartSquare
