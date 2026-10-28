import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Chow
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.TargetGraphProduct
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardComposition

/-! # Chow -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Chow

noncomputable section

/-! The graph factorization and smooth projection give the full
Chow projection formula between integral smooth projective schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier] [IsIntegral Y.carrier]
  (P : ProperCycleLinearity.ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver)
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

local instance : Smooth P.snd.left := ProductDivisorPullback.snd_smooth P

local instance : GeometricallyIntegral (show P.space.carrier ⟶ Y.carrier from P.snd.left) := by
  let : GeometricallyIntegral X.structureMap := ClosedGeometricIntegral.geometricallyIntegral X.structureMap
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk P.fst P.snd) P.isLimit)
    (inferInstance : GeometricallyIntegral X.structureMap)

theorem chow (p q s : ℕ) (hd : q + n = s + m) (a : ProperCycleLinearity.ChowQ Y p) (b : ProperCycleLinearity.ChowQ X q) :
    ChowPushforwardMap.map f m n (p + q) (p + s) (by omega)
      (General.GeneralChowIntersection.chowMap X m p q (General.ChowPullback.pull P f m n p a) b) =
      General.GeneralChowIntersection.chowMap Y n p s a (ChowPushforwardMap.map f m n q s hd b) := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y p a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q b
  let A := ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a)
  let B := ChowPushforwardMap.map (P.graph f) m (m + n) q (q + n) (by omega) (ProperCycleLinearity.cycleToChowQ X q b)
  have hs : ChowPushforwardMap.map P.snd (m + n) n (p + (q + n)) (p + s) (by omega)
      (General.GeneralChowIntersection.chowMap P.space (m + n) p (q + n) A B) =
      General.GeneralChowIntersection.chowMap Y n p s (ProperCycleLinearity.cycleToChowQ Y p a)
        (ChowPushforwardMap.map P.snd (m + n) n (q + n) s (by omega) B) := by
    dsimp only [A, B]
    rw [ChowPushforwardMap.map_mk, General.ProductPullback.secondPullback_eq_flatMap P m n p]
    exact ProjectionFormula.Smooth.Chow.Projection.chow P.snd (m + n) n p (q + n) s (by omega) a
      (ProperCycleLinearity.cyclePushforward (P.graph f) q (q + n) b)
  calc
    _ = ChowPushforwardMap.map P.snd (m + n) n (p + (q + n)) (p + s) (by omega)
        (ChowPushforwardMap.map (P.graph f) m (m + n) (p + q) (p + (q + n)) (by omega)
          (General.GeneralChowIntersection.chowMap X m p q (General.ChowPullback.pull P f m n p (ProperCycleLinearity.cycleToChowQ Y p a))
            (ProperCycleLinearity.cycleToChowQ X q b))) := by
      rw [ChowPushforwardComposition.comp, P.graph_snd]
    _ = ChowPushforwardMap.map P.snd (m + n) n (p + (q + n)) (p + s) (by omega)
        (General.GeneralChowIntersection.chowMap P.space (m + n) p (q + n) A B) :=
      congrArg (ChowPushforwardMap.map P.snd (m + n) n (p + (q + n)) (p + s) (by omega))
        (TargetGraphProduct.product P f m n p q a b)
    _ = General.GeneralChowIntersection.chowMap Y n p s (ProperCycleLinearity.cycleToChowQ Y p a)
        (ChowPushforwardMap.map P.snd (m + n) n (q + n) s (by omega) B) := hs
    _ = _ := by
      dsimp only [B]
      rw [ChowPushforwardComposition.comp, P.graph_snd]

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Chow
