import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Base Square Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli

noncomputable section

/-! A commuting square of base maps gives an actual complete polarized isomorphism between the two iterated base changes, including both abelian and dual group structures. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def Isomorphisms.LevelPreservingIso.ofEqualBaseMaps {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f h : T ⟶ S) (w : f = h) :
    Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback h) := by
  subst h
  exact Isomorphisms.LevelPreservingIso.refl (A.pullback f)

def Isomorphisms.LevelPreservingIso.baseSquare {S X Y Z : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : X ⟶ S) (h : Y ⟶ S) (p : Z ⟶ X) (q : Z ⟶ Y) (w : p ≫ f = q ≫ h) :
    Isomorphisms.LevelPreservingIso ((A.pullback f).pullback p) ((A.pullback h).pullback q) :=
  ((Isomorphisms.LevelPreservingIso.pullbackComp A f p).trans (Isomorphisms.LevelPreservingIso.ofEqualBaseMaps A (p ≫ f) (q ≫ h) w)).trans
    (Isomorphisms.LevelPreservingIso.pullbackComp A h q).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli
