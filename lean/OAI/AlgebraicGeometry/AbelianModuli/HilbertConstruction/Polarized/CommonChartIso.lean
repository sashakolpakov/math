import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareIsomorphism

/-! # Common Chart Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CommonChartIso

noncomputable section

/-! Transport original polarized full-level isomorphisms to a common
chart test using the two commuting base-map squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def polarizedCommonChartIso {S : Scheme.{u}} {G T V U W : Over S}
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N G.left)
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N U.left)
    (C : PolarizationData.PolarizedAbelianWithFullLevel g δ N W.left)
    (i : U ⟶ G) (j : W ⟶ G) (a b : T ⟶ G)
    (p : V ⟶ U) (q : V ⟶ W) (r : V ⟶ T)
    (hp : p ≫ i = r ≫ a) (hq : q ≫ j = r ≫ b)
    (ei : Moduli.Isomorphisms.LevelPreservingIso B (A.pullback i.left))
    (ej : Moduli.Isomorphisms.LevelPreservingIso C (A.pullback j.left))
    (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback a.left) (A.pullback b.left)) :
    Moduli.Isomorphisms.LevelPreservingIso (B.pullback p.left) (C.pullback q.left) :=
  let ep := (ei.pullback p.left).trans
    (Moduli.Isomorphisms.LevelPreservingIso.baseSquare A i.left a.left p.left r.left
      (congrArg Over.Hom.left hp))
  let eq := (ej.pullback q.left).trans
    (Moduli.Isomorphisms.LevelPreservingIso.baseSquare A j.left b.left q.left r.left
      (congrArg Over.Hom.left hq))
  (ep.trans (e.pullback r.left)).trans eq.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CommonChartIso
