import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.IsomorphismTransportEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Base Square Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli

noncomputable section

/-! A commuting base square identifies the complete moduli-isomorphism sets obtained by its two iterated base changes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def Isomorphisms.LevelPreservingIso.baseSquareEquiv {S X Y Z : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : X ⟶ S) (h : Y ⟶ S) (p : Z ⟶ X) (q : Z ⟶ Y) (w : p ≫ f = q ≫ h) :
    Isomorphisms.LevelPreservingIso ((A.pullback f).pullback p) ((B.pullback f).pullback p) ≃
      Isomorphisms.LevelPreservingIso ((A.pullback h).pullback q) ((B.pullback h).pullback q) :=
  ((Isomorphisms.LevelPreservingIso.transportEquiv (Isomorphisms.LevelPreservingIso.pullbackComp A f p) (Isomorphisms.LevelPreservingIso.pullbackComp B f p)).trans
    (Equiv.cast (congrArg (fun b => Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b)) w))).trans
      (Isomorphisms.LevelPreservingIso.transportEquiv (Isomorphisms.LevelPreservingIso.pullbackComp A h q) (Isomorphisms.LevelPreservingIso.pullbackComp B h q)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli
