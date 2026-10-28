import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.Codimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.InverseChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ChowFamily

/-! # Inverse Equation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.InverseEquation.BundleCycles

noncomputable section

/-! Normal inversion recovers the codimension part of every cone cycle
in every Chow dimension grade. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

theorem graphNormalInverseChow_equation (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) (d : ℕ) :
    ChowFamily.BundleCycles.graphNormalChowFamily f p d (InverseChow.BundleCycles.graphNormalInverseChow f p β) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d (Graph.SpecializationCycleCodimension.BundleCycles.graphConeCodimensionPart f p β) := by
  change ChowFamily.BundleCycles.graphNormalChowFamily f p d
    (Chow.BundleCycles.cycleToChowQ X p (Projective.CodimensionPointClass.BundleCycles.projectiveCodimensionComponent X p (InverseChow.BundleCycles.graphNormalPointPreimage f β))) = _
  rw [ChowFamily.BundleCycles.graphNormalChowFamily_cycle, Codimension.BundleCycles.graphNormalPointPullback_codimensionPart]
  exact Graph.ConeCodimensionChow.BundleCycles.graphConeCodimensionPart_chow_eq f p d _ β (InverseChow.BundleCycles.graphNormalPointPreimage_spec f β d)

theorem graphNormalInverseChow_equation_of_codimension (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ)
    (hβ : Graph.SpecializationCycleCodimension.BundleCycles.graphConeCodimensionPart f p β = β) (d : ℕ) :
    ChowFamily.BundleCycles.graphNormalChowFamily f p d (InverseChow.BundleCycles.graphNormalInverseChow f p β) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d β := by
  rw [graphNormalInverseChow_equation, hβ]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.InverseEquation.BundleCycles
