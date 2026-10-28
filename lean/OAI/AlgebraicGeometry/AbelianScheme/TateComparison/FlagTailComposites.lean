import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagRecursion
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagComposites

/-! # Flag Tail Composites -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Removing the first branch factors every actual cumulative flag
isogeny through that branch, including the canonical equality transports
at the initial points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.RealizesIsogenyQuotient)
  {k : Type} [Field k] {b : Spec (.of k) ⟶ Spec (.of K)}

theorem Data.SphericalPELAlbaneseData.c46FiberIsogeny_relabel_hom (t : Local.IntegralType s)
    (x y x' y' : D.GeometricPoint b) (c : Over.mk b ⟶ (D.correspondence t).cover)
    (hs : c ≫ (D.correspondence t).source = x) (ht : c ≫ (D.correspondence t).target = y)
    (hs' : c ≫ (D.correspondence t).source = x') (ht' : c ≫ (D.correspondence t).target = y')
    (hx : x = x') (hy : y = y') :
    eqToHom (congrArg (fun z => (D.fiberFamily b z).abelian.scheme) hx) ≫
      (D.c46FiberIsogeny h t x' y' c hs' ht').isogeny.hom =
      (D.c46FiberIsogeny h t x y c hs ht).isogeny.hom ≫
        eqToHom (congrArg (fun z => (D.fiberFamily b z).abelian.scheme) hy) := by
  cases hx
  cases hy
  exact (Category.id_comp (D.c46FiberIsogeny h t x y c hs ht).isogeny.hom).trans
    (Category.comp_id (D.c46FiberIsogeny h t x y c hs ht).isogeny.hom).symm

variable {x : D.GeometricPoint b} {t : Local.IntegralType s} {ts : List (Local.IntegralType s)}

theorem Data.SphericalPELAlbaneseData.c46FlagComposites_first_hom (F : D.PELFlag b x (t :: ts)) :
    (D.c46FlagComposites h F (Fin.succ 0)).isogeny.hom =
      (D.c46FiberIsogeny h t x ((Data.SphericalPELAlbaneseData.PELFlag.first F).val ≫ (D.correspondence t).target)
        (Data.SphericalPELAlbaneseData.PELFlag.first F).val (Data.SphericalPELAlbaneseData.PELFlag.first F).property rfl).isogeny.hom ≫
      (D.c46FlagComposites h (Data.SphericalPELAlbaneseData.PELFlag.tail F) 0).isogeny.hom := by
  change (D.compositeFromSteps F (D.c46FlagSteps h F) (Fin.succ 0)).isogeny.hom = _
  rw [D.compositeFromSteps_succ_hom]
  change (D.initialFlagIsogeny F).isogeny.hom ≫ (D.c46FlagSteps h F 0).isogeny.hom =
    _ ≫ (D.initialFlagIsogeny (Data.SphericalPELAlbaneseData.PELFlag.tail F)).isogeny.hom
  rw [D.initialFlagIsogeny_hom, D.initialFlagIsogeny_hom]
  exact D.c46FiberIsogeny_relabel_hom h t x
    ((Data.SphericalPELAlbaneseData.PELFlag.first F).val ≫ (D.correspondence t).target) (F.point 0) (F.point (Fin.succ 0))
    (F.branch 0) (Data.SphericalPELAlbaneseData.PELFlag.first F).property rfl (F.source 0) (F.target 0)
    F.start.symm (F.target 0)

theorem Data.SphericalPELAlbaneseData.c46FlagComposites_tail_hom (F : D.PELFlag b x (t :: ts)) (j : Fin (ts.length + 1)) :
    (D.c46FlagComposites h F j.succ).isogeny.hom =
      (D.c46FiberIsogeny h t x ((Data.SphericalPELAlbaneseData.PELFlag.first F).val ≫ (D.correspondence t).target)
        (Data.SphericalPELAlbaneseData.PELFlag.first F).val (Data.SphericalPELAlbaneseData.PELFlag.first F).property rfl).isogeny.hom ≫
      (D.c46FlagComposites h (Data.SphericalPELAlbaneseData.PELFlag.tail F) j).isogeny.hom := by
  induction j using Fin.induction with
  | zero => exact D.c46FlagComposites_first_hom h F
  | succ i ih =>
    change (D.compositeFromSteps F (D.c46FlagSteps h F) i.succ.succ).isogeny.hom =
      _ ≫ (D.compositeFromSteps (Data.SphericalPELAlbaneseData.PELFlag.tail F) (D.c46FlagSteps h (Data.SphericalPELAlbaneseData.PELFlag.tail F)) i.succ).isogeny.hom
    rw [D.compositeFromSteps_succ_hom, D.compositeFromSteps_succ_hom]
    change (D.c46FlagComposites h F i.castSucc.succ).isogeny.hom ≫
      (D.c46FlagSteps h F i.succ).isogeny.hom = _
    rw [ih]
    exact Category.assoc
      (D.c46FiberIsogeny h t x ((Data.SphericalPELAlbaneseData.PELFlag.first F).val ≫ (D.correspondence t).target)
        (Data.SphericalPELAlbaneseData.PELFlag.first F).val (Data.SphericalPELAlbaneseData.PELFlag.first F).property rfl).isogeny.hom
      (D.c46FlagComposites h (Data.SphericalPELAlbaneseData.PELFlag.tail F) i.castSucc).isogeny.hom
      (D.c46FlagSteps h (Data.SphericalPELAlbaneseData.PELFlag.tail F) i).isogeny.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
