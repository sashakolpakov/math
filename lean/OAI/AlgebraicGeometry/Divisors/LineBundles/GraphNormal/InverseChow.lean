import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.PointPreimage
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.DimensionDetection

/-! # Inverse Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.InverseChow.BundleCycles

noncomputable section

section

/-! A finite normal-cone cycle has a well-defined codimension Chow class
on the source, independent of its actual point-cycle preimage. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphNormalPointPreimage (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) : X.carrier →₀ ℚ :=
  Classical.choose (PointPreimage.BundleCycles.graphNormalPointChow_preimage f β)

theorem graphNormalPointPreimage_spec (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) (d : ℕ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d (Graph.Chow.BundleCycles.graphNormalPointPullback f (graphNormalPointPreimage f β)) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d β :=
  Classical.choose_spec (PointPreimage.BundleCycles.graphNormalPointChow_preimage f β) d

def graphNormalInverseChowValue (p : ℕ) (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) : Chow.BundleCycles.ChowQ X p :=
  Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p (graphNormalPointPreimage f β)

theorem graphNormalInverseChowValue_eq_of_preimage (p : ℕ)
    (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) (z : X.carrier →₀ ℚ)
    (hz : ∀ d : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d (Graph.Chow.BundleCycles.graphNormalPointPullback f z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d β) :
    graphNormalInverseChowValue f p β = Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p z := by
  have H := ChowJointDetection.BundleCycles.graphNormalPointChow_joint_equal f (graphNormalPointPreimage f β) z
    (fun d => (graphNormalPointPreimage_spec f β d).trans (hz d).symm)
  have Hzero := ProjectiveChow.DimensionDetection.BundleCycles.projectivePointChowClass_eq_zero_of_all_dimensions X p (graphNormalPointPreimage f β - z) (by
    intro d
    rw [map_sub, H d, sub_self])
  rw [map_sub] at Hzero
  exact sub_eq_zero.mp Hzero

end

/-! Inverting actual normal extension and taking a codimension component
is a linear map on finite normal-cone cycles and kills their Chow relations. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

def graphNormalInverseChow : (Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ) →ₗ[ℚ] Chow.BundleCycles.ChowQ X p where
  toFun := graphNormalInverseChowValue f p
  map_add' β γ := by
    calc
      _ = Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p (graphNormalPointPreimage f β + graphNormalPointPreimage f γ) := by
        apply graphNormalInverseChowValue_eq_of_preimage f p
        intro d
        rw [map_add, map_add, map_add, graphNormalPointPreimage_spec, graphNormalPointPreimage_spec]
      _ = _ := map_add (Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p) _ _
  map_smul' a β := by
    calc
      _ = Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p (a • graphNormalPointPreimage f β) := by
        apply graphNormalInverseChowValue_eq_of_preimage f p
        intro d
        rw [map_smul, map_smul, map_smul, graphNormalPointPreimage_spec]
      _ = _ := map_smul (Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p) _ _

theorem graphNormalInverseChow_extension (z : X.carrier →₀ ℚ) :
    graphNormalInverseChow f p (Graph.Chow.BundleCycles.graphNormalPointPullback f z) = Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p z :=
  graphNormalInverseChowValue_eq_of_preimage f p _ z (fun _ => rfl)

theorem graphNormalInverseChow_eq_zero_of_all_dimensions (β : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ)
    (hβ : ∀ d : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d β = 0) :
    graphNormalInverseChow f p β = 0 := by
  have H := graphNormalInverseChowValue_eq_of_preimage f p β 0 (by
    intro d
    rw [map_zero, map_zero, hβ d])
  exact H.trans (map_zero (Projective.CodimensionPointClass.BundleCycles.projectivePointChowClass X p))

theorem graphNormalInverseChow_eq_of_all_dimensions (β γ : Global.SpecialFiber.BundleCycles.globalSpecialFiber (Graph.OpenAmbient.BundleCycles.graph f).ker →₀ ℚ)
    (hβγ : ∀ d : ℕ, Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d β =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d γ) :
    graphNormalInverseChow f p β = graphNormalInverseChow f p γ := by
  have H := graphNormalInverseChow_eq_zero_of_all_dimensions f p (β - γ) (by
    intro d
    rw [map_sub, hβγ d, sub_self])
  exact sub_eq_zero.mp ((map_sub (graphNormalInverseChow f p) β γ).symm.trans H)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.InverseChow.BundleCycles
