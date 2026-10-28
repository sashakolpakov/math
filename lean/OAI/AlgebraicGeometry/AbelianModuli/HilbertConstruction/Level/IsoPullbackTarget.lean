import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Iso Pullback Target -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Normalize the target base map before composing the original
polarized pullback-composition isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def Moduli.Isomorphisms.LevelPreservingIso.transPullbackCompOfEq
    {S U V : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (F : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (a : U ⟶ S) (q : V ⟶ U) (b : V ⟶ S) (hb : b = q ≫ a)
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N V}
    (e : Moduli.Isomorphisms.LevelPreservingIso A (F.pullback b)) :
    Moduli.Isomorphisms.LevelPreservingIso A ((F.pullback a).pullback q) := by
  subst b
  exact e.trans (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp F a q).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
