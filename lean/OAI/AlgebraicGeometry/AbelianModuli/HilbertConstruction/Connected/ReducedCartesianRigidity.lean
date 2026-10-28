import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedGlobalRigidity

/-! # Reduced Cartesian Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedCartesianRigidity

noncomputable section

/-! Global rigidity can be checked by a constant morphism on an actual field-valued base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S Y F : Scheme.{u}} {K : Type u} [Field K]

theorem connectedReducedFamily_globalRigidity_of_fiberMap (p : X ⟶ S) (hp : IsOpenMap p)
    [PreconnectedSpace S] [IsReduced X]
    [UniversallyClosed p] [GeometricallyConnected p] [GeometricallyReduced p] (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (f : X ⟶ Y) [Y.IsSeparated] (b : Spec (.of K) ⟶ S) (a : Spec (.of K) ⟶ Y)
    (hf : pullback.fst p b ≫ f = pullback.snd p b ≫ a) : f = p ≫ σ ≫ f := by
  let t : Spec (.of K) := default
  apply ReducedGlobalRigidity.connectedReducedFamily_globalRigidity p hp σ hσ f (b t) (a t)
  intro x hx
  have hr : x ∈ Set.range (pullback.fst p b) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨t, hx.symm⟩
  obtain ⟨z, rfl⟩ := hr
  exact (congrArg (fun k : pullback p b ⟶ Y => k z) hf).trans
    (congrArg (fun s : Spec (.of K) => a s) (Subsingleton.elim (pullback.snd p b z) t))

theorem connectedReducedFamily_globalRigidity_of_cartesianFiber (p : X ⟶ S) (hp : IsOpenMap p)
    [PreconnectedSpace S] [IsReduced X]
    [UniversallyClosed p] [GeometricallyConnected p] [GeometricallyReduced p] (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (f : X ⟶ Y) [Y.IsSeparated] (b : Spec (.of K) ⟶ S) (a : Spec (.of K) ⟶ Y)
    (j : F ⟶ X) (q : F ⟶ Spec (.of K)) (H : IsPullback j q p b)
    (hf : j ≫ f = q ≫ a) : f = p ≫ σ ≫ f := by
  apply connectedReducedFamily_globalRigidity_of_fiberMap p hp σ hσ f b a
  rw [← H.isoPullback_inv_fst, ← H.isoPullback_inv_snd, Category.assoc, hf, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedCartesianRigidity
