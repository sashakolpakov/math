import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.NonreducedTrace
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange

/-! # Branch Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual branch splittings and their sheet maps commute with arbitrary
base change of the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange

universe u

theorem BranchBaseChange.overPullback_map_fst {S S' : Scheme.{u}} (a : S' ⟶ S)
    {Y Z : Over S} (f : Y ⟶ Z) :
    ((Over.pullback a).map f).left ≫ pullback.fst Z.hom a =
      pullback.fst Y.hom a ≫ f.left := pullback.lift_fst _ _ _

theorem BranchBaseChange.constantSchemeBaseChangeIso_inclusion {S S' : Scheme.{u}} (a : S' ⟶ S)
    (I : Type u) (i : I) :
    Sigma.ι (fun _ : I => S') i ≫ (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a I).hom.left ≫
      pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom a = a ≫ Sigma.ι (fun _ : I => S) i := by
  let r := AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSetRepresentable S' I
  let r' := AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSetPullbackRepresentable a I
  have he : r'.homEquiv (TateComparison.BranchSplitting.constantCoproductInclusion S' I i ≫ (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a I).hom) =
      r.homEquiv (TateComparison.BranchSplitting.constantCoproductInclusion S' I i) := by
    change r'.homEquiv (TateComparison.BranchSplitting.constantCoproductInclusion S' I i ≫
      r'.homEquiv.symm (r.homEquiv (𝟙 _))) = _
    rw [r'.comp_homEquiv_symm, Equiv.apply_symm_apply, ← r.homEquiv_comp, Category.comp_id]
  let f := Sigma.ι (fun _ : I => S') i ≫ (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a I).hom.left ≫
    pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom a
  have hf : ∀ z, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S I (f z) = i := by
    intro z
    have h := congrArg (fun c : LocallyConstant S' I => c z) he
    change AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S I (f z) = AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S' I (Sigma.ι (fun _ : I => S') i z) at h
    exact h.trans (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i z)
  have hb : f ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom = a := by
    have h := (((Over.mapPullbackAdj a).homEquiv (Over.mk (𝟙 S')) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I)).symm
      (TateComparison.BranchSplitting.constantCoproductInclusion S' I i ≫ (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a I).hom)).w
    change ((Sigma.ι (fun _ : I => S') i ≫ (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a I).hom.left) ≫
      pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom a) ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom = (𝟙 S') ≫ a at h
    exact (congrArg (fun z => z ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom)
      (Category.assoc _ _ _).symm).trans (h.trans (Category.id_comp a))
  exact (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_factor f i hf).trans (congrArg (fun z => z ≫ Sigma.ι (fun _ : I => S) i) hb)

variable {B : Scheme.{0}} {X : Over B} (C : Correspondences.EtaleCorrespondence X)
  {T T' : Over B} (x : T ⟶ X) (a : T' ⟶ T)

def Correspondences.EtaleCorrespondence.fiberBaseChangeIso :
    (Over.pullback a.left).obj (Over.mk (pullback.snd C.source.left x.left)) ≅
      Over.mk (pullback.snd C.source.left (a ≫ x).left) :=
  Over.isoMk (pullbackLeftPullbackSndIso C.source.left x.left a.left)
    (pullbackLeftPullbackSndIso_hom_snd _ _ _)

theorem Correspondences.EtaleCorrespondence.fiberBaseChangeIso_hom_fst :
    (C.fiberBaseChangeIso x a).hom.left ≫ pullback.fst C.source.left (a ≫ x).left =
      pullback.fst (pullback.snd C.source.left x.left) a.left ≫ pullback.fst C.source.left x.left :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

def Correspondences.EtaleCorrespondence.pullbackBranchSplitting {n : ℕ} (e : C.BranchSplitting x n) :
    C.BranchSplitting (a ≫ x) n :=
  TateComparison.BranchSplitting.constantCoproductIso T'.left (Fin n) ≪≫ AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a.left (Fin n) ≪≫
    (Over.pullback a.left).mapIso (C.splitConstantIso x e) ≪≫ C.fiberBaseChangeIso x a

theorem Correspondences.EtaleCorrespondence.pullbackBranchSplitting_constant {n : ℕ} (e : C.BranchSplitting x n) :
    C.splitConstantIso (a ≫ x) (C.pullbackBranchSplitting x a e) =
      AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a.left (Fin n) ≪≫
        (Over.pullback a.left).mapIso (C.splitConstantIso x e) ≪≫ C.fiberBaseChangeIso x a := by
  apply Iso.ext
  simp only [Correspondences.EtaleCorrespondence.splitConstantIso, Correspondences.EtaleCorrespondence.pullbackBranchSplitting, Iso.trans_hom,
    Iso.symm_hom, Iso.inv_hom_id_assoc]

theorem Correspondences.EtaleCorrespondence.splitBranch_constant_over {n : ℕ} (e : C.BranchSplitting x n) (i : Fin n) :
    (C.splitBranch x e i).val.left =
      (TateComparison.BranchSplitting.constantCoproductInclusion T.left (Fin n) i ≫ (C.splitConstantIso x e).hom).left ≫
        pullback.fst C.source.left x.left := by
  have h : TateComparison.BranchSplitting.constantCoproductInclusion T.left (Fin n) i ≫ (C.splitConstantIso x e).hom =
      Sigma.ι (fun _ : Fin n => Over.mk (𝟙 T.left)) i ≫ e.hom := by
    simp only [Correspondences.EtaleCorrespondence.splitConstantIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
      TateComparison.BranchSplitting.constantCoproductInclusion_inv]
  exact congrArg (fun f => f.left ≫ pullback.fst C.source.left x.left) h.symm

theorem Correspondences.EtaleCorrespondence.splitBranch_pullback {n : ℕ} (e : C.BranchSplitting x n) (i : Fin n) :
    (C.splitBranch (a ≫ x) (C.pullbackBranchSplitting x a e) i).val =
      a ≫ (C.splitBranch x e i).val := by
  apply Over.OverMorphism.ext
  change (C.splitBranch (a ≫ x) (C.pullbackBranchSplitting x a e) i).val.left =
    a.left ≫ (C.splitBranch x e i).val.left
  rw [Correspondences.EtaleCorrespondence.splitBranch_constant_over, Correspondences.EtaleCorrespondence.pullbackBranchSplitting_constant, Correspondences.EtaleCorrespondence.splitBranch_constant_over]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Over.comp_left, Category.assoc]
  have hF := C.fiberBaseChangeIso_hom_fst x a
  change (C.fiberBaseChangeIso x a).hom.left ≫ pullback.fst C.source.left (a.left ≫ x.left) =
    pullback.fst (pullback.snd C.source.left x.left) a.left ≫ pullback.fst C.source.left x.left at hF
  rw [hF]
  have hM := BranchBaseChange.overPullback_map_fst a.left (C.splitConstantIso x e).hom
  change ((Over.pullback a.left).map (C.splitConstantIso x e).hom).left ≫
    pullback.fst (pullback.snd C.source.left x.left) a.left =
      pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme T.left (Fin n)).hom a.left ≫ (C.splitConstantIso x e).hom.left at hM
  rw [← Category.assoc ((Over.pullback a.left).map (C.splitConstantIso x e).hom).left,
    hM]
  simp only [Category.assoc]
  have hi : (TateComparison.BranchSplitting.constantCoproductInclusion T'.left (Fin n) i).left ≫
      (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a.left (Fin n)).hom.left ≫
      pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme T.left (Fin n)).hom a.left =
        a.left ≫ (TateComparison.BranchSplitting.constantCoproductInclusion T.left (Fin n) i).left :=
    BranchBaseChange.constantSchemeBaseChangeIso_inclusion a.left (Fin n) i
  rw [← Category.assoc (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso a.left (Fin n)).hom.left,
    ← Category.assoc (TateComparison.BranchSplitting.constantCoproductInclusion T'.left (Fin n) i).left, hi]
  simp only [Category.assoc]

theorem Correspondences.EtaleCorrespondence.localTraceMap_pullback {A : Over B} [GrpObj A] [IsCommMonObj A]
    (f : X ⟶ A) {n : ℕ} (e : C.BranchSplitting x n) :
    C.localTraceMap f (a ≫ x) (C.pullbackBranchSplitting x a e) = a ≫ C.localTraceMap f x e := by
  change (∏ i : Fin n, C.endpoint (C.splitBranch (a ≫ x) (C.pullbackBranchSplitting x a e) i) ≫ f) =
    Correspondences.EtaleCorrespondence.precompPointHom a (∏ i : Fin n, C.endpoint (C.splitBranch x e i) ≫ f)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Correspondences.EtaleCorrespondence.endpoint, Correspondences.EtaleCorrespondence.splitBranch_pullback, Correspondences.EtaleCorrespondence.precompPointHom, MonoidHom.coe_mk,
    OneHom.coe_mk, Category.assoc]

theorem Correspondences.EtaleCorrespondence.localTraceMap_eq_all {A : Over B} [GrpObj A] [IsCommMonObj A]
    (f : X ⟶ A) {x x' : T ⟶ X} (h : x = x') {n m : ℕ}
    (e : C.BranchSplitting x n) (e' : C.BranchSplitting x' m) :
    C.localTraceMap f x e = C.localTraceMap f x' e' := by
  subst x'
  exact C.localTraceMap_independent_all x f e e'

theorem Correspondences.EtaleCorrespondence.localTraceMap_overlap_all {A : Over B} [GrpObj A] [IsCommMonObj A]
    (f : X ⟶ A) (x' : T' ⟶ X) {n m : ℕ}
    (e : C.BranchSplitting x n) (e' : C.BranchSplitting x' m)
    {W : Over B} (a : W ⟶ T) (a' : W ⟶ T') (h : a ≫ x = a' ≫ x') :
    a ≫ C.localTraceMap f x e = a' ≫ C.localTraceMap f x' e' :=
  (C.localTraceMap_pullback x a f e).symm.trans
    ((C.localTraceMap_eq_all f h (C.pullbackBranchSplitting x a e)
      (C.pullbackBranchSplitting x' a' e')).trans (C.localTraceMap_pullback x' a' f e'))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
