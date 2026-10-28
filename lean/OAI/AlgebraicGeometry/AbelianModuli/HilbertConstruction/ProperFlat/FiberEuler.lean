import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiberEuler

/-! # Fiber Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberEuler

noncomputable section

/-! Proper flat line-bundle families over Noetherian affine bases have locally constant genuine fiber Euler characteristic. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem properFlat_fiberEuler_isLocallyConstant
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) :
    IsLocallyConstant (Geometric.FiberEuler.fiberEulerCharacteristic f L) := by
  obtain ⟨D, ⟨N, hb⟩, hf, hp, _, he⟩ := FiberwiseCohomologyModel.properFlat_exists_fiberwise_cohomology_model f L
  have hfun : Geometric.FiberEuler.fiberEulerCharacteristic f L =
      fun x => Finite.ProjectiveEulerFunction.finiteProjectiveEulerAt D (N + 1) (S.toSpecΓ x) := by
    funext x
    exact Geometric.FiberEuler.fiberEulerCharacteristic_eq_modelEuler f L x D N hf hp hb (he x)
  rw [hfun]
  exact (Finite.ProjectiveEulerFunction.finiteProjectiveEulerAt_isLocallyConstant D (N + 1) hf hp).comp_continuous S.toSpecΓ.continuous

theorem properFlat_fiberEuler_eq_of_preconnected
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [PreconnectedSpace S]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) (x y : S) :
    Geometric.FiberEuler.fiberEulerCharacteristic f L x = Geometric.FiberEuler.fiberEulerCharacteristic f L y :=
  (properFlat_fiberEuler_isLocallyConstant f L).apply_eq_of_preconnectedSpace x y

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberEuler
