import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.IsomorphismBaseEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackIsoComparison

/-! # Parameter Point Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli

noncomputable section

/-! Specializing a complete moduli isomorphism has exactly the geometric base change of its abelian map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T M : Over S} (c : T ⟶ M)
    (e : Isomorphisms.LevelPreservingIso (A.pullback M.hom) (B.pullback M.hom)) :
    (Isomorphisms.LevelPreservingIso.atParameterPoint A B c e).abelian.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c e.abelian.hom := by
  unfold Isomorphisms.LevelPreservingIso.atParameterPoint
  rw [Isomorphisms.LevelPreservingIso.baseEquality_abelian_hom A B (c.left ≫ M.hom) T.hom c.w]
  dsimp only [Isomorphisms.LevelPreservingIso.trans, Isomorphisms.LevelPreservingIso.symm, Isomorphisms.LevelPreservingIso.pullbackComp, Isomorphisms.LevelPreservingIso.pullback, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change (eqToIso (congrArg (fun b => (Over.pullback b).obj A.abelian.scheme) c.w.symm)).hom ≫
    (((A.abelian.pullbackCompIso M.hom c.left).hom ≫ (Over.pullback c.left).map e.abelian.hom) ≫
      (B.abelian.pullbackCompIso M.hom c.left).inv) ≫
        (eqToIso (congrArg (fun b => (Over.pullback b).obj B.abelian.scheme) c.w)).hom = _
  rw [Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  have hA := ParameterPullbackIsoComparison.overBaseMapPullbackIso_eq_singleParameter c A.abelian.scheme
  have hB := ParameterPullbackIsoComparison.overBaseMapPullbackIso_eq_singleParameter c B.abelian.scheme
  unfold Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange
  rw [← hA, ← hB]
  simp only [HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  let a := (Over.pullbackComp c.left M.hom).hom.app A.abelian.scheme
  let b := (Over.pullback c.left).map e.abelian.hom
  let d := (Over.pullbackComp c.left M.hom).inv.app B.abelian.scheme
  let x := eqToHom (congrArg (fun f => (Over.pullback f).obj A.abelian.scheme) c.w.symm)
  let y := eqToHom (congrArg (fun f => (Over.pullback f).obj B.abelian.scheme) c.w)
  exact congrArg (fun z => x ≫ z) ((Category.assoc (a ≫ b) d y).trans (Category.assoc a b (d ≫ y)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli
