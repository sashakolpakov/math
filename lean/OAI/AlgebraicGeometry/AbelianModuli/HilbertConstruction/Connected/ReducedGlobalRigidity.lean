import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedFamilyLocalRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.FiberEquality

/-! # Reduced Global Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedGlobalRigidity

noncomputable section

/-! Global rigidity for an open proper family with connected reduced geometric fibers over a connected base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S Y : Scheme.{u}}

theorem connectedReducedFamily_globalRigidity (p : X ⟶ S) (hp : IsOpenMap p)
    [PreconnectedSpace S] [IsReduced X] [UniversallyClosed p]
    [GeometricallyConnected p] [GeometricallyReduced p]
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _) (f : X ⟶ Y) [Y.IsSeparated]
    (s : S) (y : Y) (hy : ∀ x : X, p x = s → f x = y) : f = p ≫ σ ≫ f := by
  apply FiberEquality.connectedFamily_eq_of_localEquality p hp f (p ≫ σ ≫ f)
  · intro t ht
    apply ReducedFamilyLocalRigidity.connectedReducedFamily_localRigidity p σ hσ f t (f (σ t))
    intro x hx
    have he := EqualizerFiberLocus.equalizerFiberLocus_map_eq p f (p ≫ σ ≫ f) t ht x hx
    change f x = f (σ (p x)) at he
    exact he.trans (congrArg (fun a => f (σ a)) hx)
  · obtain ⟨V, hs, hV⟩ := ReducedFamilyLocalRigidity.connectedReducedFamily_localRigidity p σ hσ f s y hy
    exact ⟨s, EqualizerFiberLocus.restrictionEq_le_equalizerFiberLocus p f (p ≫ σ ≫ f) V hV hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedGlobalRigidity
