import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FamilyIsoBaseChange

/-! # Isomorphism Parameter Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli

noncomputable section

/-! A moduli isomorphism over a parameter scheme specializes to the original polarized families over every parameter-valued test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def Isomorphisms.LevelPreservingIso.atParameterPoint {T M : Over S} (c : T ⟶ M)
    (e : Isomorphisms.LevelPreservingIso (A.pullback M.hom) (B.pullback M.hom)) :
    Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) := by
  let d : Isomorphisms.LevelPreservingIso (A.pullback (c.left ≫ M.hom)) (B.pullback (c.left ≫ M.hom)) :=
    ((Isomorphisms.LevelPreservingIso.pullbackComp A M.hom c.left).symm.trans (e.pullback c.left)).trans
      (Isomorphisms.LevelPreservingIso.pullbackComp B M.hom c.left)
  exact (congrArg (fun b => Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b)) c.w).mp d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli
