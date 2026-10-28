import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

/-! # Fiber Iso Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.FiberIsoNaturality

noncomputable section

/-! Actual quotient-fiber comparisons are natural in morphisms of the original line sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

variable {S : Scheme.{u}} {K E : Over S} (p : K ⟶ E)
  (L M : Line.Bundles.LineBundle E.left) (e : L.sheaf ⟶ M.sheaf)

/-- The original sheaf map commutes with the actual comparison at any specified quotient point. -/
theorem comparison_hom {T : Over S} (x : T ⟶ K) (a : T ⟶ E) (hx : x ≫ p = a) :
    (Scheme.Modules.pullback x.left).map ((Scheme.Modules.pullback p.left).map e) ≫
      (LineBilinear.fiberComparison p M x a hx).hom =
    (LineBilinear.fiberComparison p L x a hx).hom ≫ (Scheme.Modules.pullback a.left).map e := by
  unfold LineBilinear.fiberComparison
  rw [GlobalPullbackFrame.comparison_eq p M x a hx, GlobalPullbackFrame.comparison_eq p L x a hx]
  exact (Scheme.Modules.pullbackComp x.left p.left ≪≫
    Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hx)).hom.naturality e

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.FiberIsoNaturality
