import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.IsomorphismTransportEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.IsomorphismNormalization

/-! # Isomorphism Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Complete isomorphisms of iterated parameter families and of the original test families are canonically equivalent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T M : Over S} (c : T ⟶ M) :
    Moduli.Isomorphisms.LevelPreservingIso ((A.pullback M.hom).pullback c.left) ((B.pullback M.hom).pullback c.left) ≃
      Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) :=
  (Moduli.Isomorphisms.LevelPreservingIso.transportEquiv (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A M.hom c.left) (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp B M.hom c.left)).trans
    (Equiv.cast (congrArg (fun b => Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b)) c.w))

theorem Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv_apply
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T M : Over S} (c : T ⟶ M)
    (e : Moduli.Isomorphisms.LevelPreservingIso ((A.pullback M.hom).pullback c.left) ((B.pullback M.hom).pullback c.left)) :
    Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv A B c e = Moduli.Isomorphisms.LevelPreservingIso.fromIteratedParameterPoint A B c e := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
