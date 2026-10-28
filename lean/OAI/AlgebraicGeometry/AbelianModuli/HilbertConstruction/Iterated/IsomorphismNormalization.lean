import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.IsomorphismBaseEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackIsoComparison

/-! # Isomorphism Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A complete isomorphism between iterated parameter pullbacks transports to the original test-family pullbacks, with its abelian map explicitly identified. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) {T M : Over S} (c : T ⟶ M)

def Moduli.Isomorphisms.LevelPreservingIso.fromIteratedParameterPoint
    (e : Moduli.Isomorphisms.LevelPreservingIso ((A.pullback M.hom).pullback c.left) ((B.pullback M.hom).pullback c.left)) :
    Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) := by
  let d := ((Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A M.hom c.left).symm.trans e).trans (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp B M.hom c.left)
  exact (congrArg (fun b => Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b)) c.w).mp d

theorem Moduli.Isomorphisms.LevelPreservingIso.fromIteratedParameterPoint_abelian_hom
    (e : Moduli.Isomorphisms.LevelPreservingIso ((A.pullback M.hom).pullback c.left) ((B.pullback M.hom).pullback c.left)) :
    (Moduli.Isomorphisms.LevelPreservingIso.fromIteratedParameterPoint A B c e).abelian.hom = HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackMorphism c e.abelian.hom := by
  unfold Moduli.Isomorphisms.LevelPreservingIso.fromIteratedParameterPoint
  rw [Moduli.Isomorphisms.LevelPreservingIso.baseEquality_abelian_hom A B (c.left ≫ M.hom) T.hom c.w]
  dsimp only [Moduli.Isomorphisms.LevelPreservingIso.trans, Moduli.Isomorphisms.LevelPreservingIso.symm, Moduli.Isomorphisms.LevelPreservingIso.pullbackComp]
  change (eqToIso (congrArg (fun b => (Over.pullback b).obj A.abelian.scheme) c.w.symm)).hom ≫
    (((A.abelian.pullbackCompIso M.hom c.left).hom ≫ e.abelian.hom) ≫
      (B.abelian.pullbackCompIso M.hom c.left).inv) ≫
        (eqToIso (congrArg (fun b => (Over.pullback b).obj B.abelian.scheme) c.w)).hom = _
  rw [Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  simp only [HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackMorphism, HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackIso, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  let a := (Over.pullbackComp c.left M.hom).hom.app A.abelian.scheme
  let d := (Over.pullbackComp c.left M.hom).inv.app B.abelian.scheme
  let x := eqToHom (congrArg (fun f => (Over.pullback f).obj A.abelian.scheme) c.w.symm)
  let y := eqToHom (congrArg (fun f => (Over.pullback f).obj B.abelian.scheme) c.w)
  exact congrArg (fun z => x ≫ z)
    ((Category.assoc (a ≫ e.abelian.hom) d y).trans (Category.assoc a e.abelian.hom (d ≫ y)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
