import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsLocalRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.FiberEquality

/-! # Functions Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsRigidity

noncomputable section

/-! Global-functions rigidity propagates across connected parameter schemes, including nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X T Y : Scheme.{u}}

theorem globalFunctions_globalRigidity (p : X ⟶ T) [UniversallyClosed p]
    (hp : ∀ V : T.Opens, IsIso (p ∣_ V).appTop) (hopen : IsOpenMap p)
    [PreconnectedSpace T] (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 _) (f : X ⟶ Y) [Y.IsSeparated]
    (s : T) (y : Y) (hy : ∀ x : X, p x = s → f x = y) : f = p ≫ σ ≫ f := by
  apply Connected.FiberEquality.connectedFamily_eq_of_localEquality p hopen f (p ≫ σ ≫ f)
  · intro t ht
    apply FunctionsLocalRigidity.globalFunctions_localRigidity p hp σ hσ f t (f (σ t))
    intro x hx
    have he := EqualizerFiberLocus.equalizerFiberLocus_map_eq p f (p ≫ σ ≫ f) t ht x hx
    change f x = f (σ (p x)) at he
    exact he.trans (congrArg (fun a => f (σ a)) hx)
  · obtain ⟨V, hs, hV⟩ := FunctionsLocalRigidity.globalFunctions_localRigidity p hp σ hσ f s y hy
    exact ⟨s, EqualizerFiberLocus.restrictionEq_le_equalizerFiberLocus p f (p ≫ σ ≫ f) V hV hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsRigidity
