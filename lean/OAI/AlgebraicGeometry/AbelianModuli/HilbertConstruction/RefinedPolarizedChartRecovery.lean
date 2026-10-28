import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareIsomorphism

/-! # Refined Polarized Chart Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RefinedPolarizedChartRecovery

noncomputable section

/-! Recover the original polarized chart family through equal base
maps and the canonical comparison with an iterated pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def refinedPolarizedChartIso
    {S U V : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N U)
    (t a : V ⟶ U) (c : V ⟶ S) (f : U ⟶ S)
    (hs : a = t) (ht : c = t ≫ f)
    (e : Moduli.Isomorphisms.LevelPreservingIso (B.pullback a) (A.pullback c)) :
    Moduli.Isomorphisms.LevelPreservingIso (B.pullback t) ((A.pullback f).pullback t) :=
  ((Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps B t a hs.symm).trans e).trans
    ((Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps A c (t ≫ f) ht).trans
      (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f t).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RefinedPolarizedChartRecovery
