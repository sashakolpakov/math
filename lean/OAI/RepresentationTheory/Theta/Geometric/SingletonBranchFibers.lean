import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchFibers
import OAI.RepresentationTheory.Theta.Geometric.Dual.BranchSplitting

/-! # Singleton Branch Fibers -/

namespace OAI.RepresentationTheory.Theta.Geometric.SingletonBranchFibers

noncomputable section

/-! A splitting enumerates every branch over a test scheme with one
underlying point, including nonreduced dual-number tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchFibers

def constantSingletonPointsEquiv (S : Scheme) (I : Type) (T : Over S) [Unique T.left] :
    (T ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I) ≃ I :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I T).trans {
    toFun c := c default
    invFun i := LocallyConstant.const _ i
    left_inv c := LocallyConstant.ext (fun x => congrArg c (Subsingleton.elim default x))
    right_inv _ := rfl }

def constantSingletonPoint (S : Scheme) (I : Type) (T : Over S) (i : I) :
    T ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I :=
  Over.homMk (T.hom ≫ Sigma.ι (fun _ : I => S) i) (by
    change (T.hom ≫ Sigma.ι (fun _ : I => S) i) ≫ Sigma.desc (fun _ : I => 𝟙 S) = T.hom
    rw [Category.assoc, Sigma.ι_comp_desc, Category.comp_id])

theorem constantSingletonPointsEquiv_point (S : Scheme) (I : Type) (T : Over S)
    [Unique T.left] (i : I) :
    constantSingletonPointsEquiv S I T (constantSingletonPoint S I T i) = i :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i (T.hom default)

theorem constantSingletonPointsEquiv_symm (S : Scheme) (I : Type) (T : Over S)
    [Unique T.left] (i : I) :
    (constantSingletonPointsEquiv S I T).symm i = constantSingletonPoint S I T i :=
  (constantSingletonPointsEquiv S I T).symm_apply_eq.mpr
    (constantSingletonPointsEquiv_point S I T i).symm

def splitSingletonFiberEquiv {B : Scheme} {X : Over B} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    {T T' : Over B} (t : T ⟶ X) (a : T' ⟶ T) [Unique T'.left]
    {n : ℕ} (e : C.BranchSplitting t n) : Fin n ≃ C.Fiber (a ≫ t) := by
  let : Unique (Over.mk a.left).left := inferInstanceAs (Unique T'.left)
  exact (constantSingletonPointsEquiv T.left (Fin n) (Over.mk a.left)).symm.trans
    ((Iso.homCongr (Iso.refl _)
      ((AlgebraicGeometry.AbelianScheme.TateComparison.BranchSplitting.constantCoproductIso T.left (Fin n)).symm ≪≫ e)).trans
        (C.relativeFiberSectionEquiv t a).symm)

theorem splitSingletonFiberEquiv_val {B : Scheme} {X : Over B} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    {T T' : Over B} (t : T ⟶ X) (a : T' ⟶ T) [Unique T'.left]
    {n : ℕ} (e : C.BranchSplitting t n) (i : Fin n) :
    (splitSingletonFiberEquiv C t a e i).val = a ≫ (C.splitBranch t e i).val := by
  let : Unique (Over.mk a.left).left := inferInstanceAs (Unique T'.left)
  simp only [splitSingletonFiberEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Iso.trans_hom, Iso.symm_hom, constantSingletonPointsEquiv_symm]
  apply Over.OverMorphism.ext
  change (((a.left ≫ Sigma.ι (fun _ : Fin n => T.left) i) ≫
    (Sigma.desc (fun j : Fin n => (Sigma.ι (fun _ : Fin n => Over.mk (𝟙 T.left)) j).left)) ≫ e.hom.left) ≫
      pullback.fst C.source.left t.left) =
    a.left ≫ ((Sigma.ι (fun _ : Fin n => Over.mk (𝟙 T.left)) i).left ≫ e.hom.left) ≫
      pullback.fst C.source.left t.left
  simp only [Category.assoc, Sigma.ι_comp_desc_assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.SingletonBranchFibers
