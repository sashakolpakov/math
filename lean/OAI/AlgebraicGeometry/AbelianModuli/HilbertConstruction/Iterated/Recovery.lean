import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.IsomorphismEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.BaseMapMorphismEquality

/-! # Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An isomorphism transported to iterated parameter families recovers the pulled-back ambient abelian map whenever its original abelian map is the geometric specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv_symm_abelian_hom
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T M : Over S} (c : T ⟶ M)
    (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom))
    (f : (A.pullback M.hom).abelian.scheme ⟶ (B.pullback M.hom).abelian.scheme)
    (h : e.abelian.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f) :
    ((Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv A B c).symm e).abelian.hom = (Over.pullback c.left).map f := by
  let q := (Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv A B c).symm e
  have hq : Moduli.Isomorphisms.LevelPreservingIso.fromIteratedParameterPoint A B c q = e :=
    (Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv_apply A B c q).symm.trans ((Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv A B c).apply_symm_apply e)
  have hmap := Moduli.Isomorphisms.LevelPreservingIso.fromIteratedParameterPoint_abelian_hom A B c q
  apply HilbertConstruction.Over.BaseMapMorphismEquality.overBaseMapPullbackMorphism_injective c
  exact hmap.symm.trans ((congrArg (fun z => z.abelian.hom) hq).trans
    (h.trans (HilbertConstruction.Over.BaseMapMorphismEquality.overBaseMapPullbackMorphism_pullback c f).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
