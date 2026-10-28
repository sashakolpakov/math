import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchSplitting

/-! # Branch Fibers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! A genuine branch splitting enumerates every geometric source-fiber
point exactly once, with its original target map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

section ConstantPoints

universe u
variable (S : Scheme.{u}) (I : Type u) {k : Type u} [Field k]
  (b : Spec (.of k) ⟶ S)

def BranchFibers.constantFieldPointsEquiv : (Over.mk b ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I) ≃ I := by
  let : Unique (Over.mk b).left := inferInstanceAs (Unique (Spec (.of k)))
  exact (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I (Over.mk b)).trans {
    toFun c := c default
    invFun i := LocallyConstant.const _ i
    left_inv c := LocallyConstant.ext (fun x => congrArg c (Subsingleton.elim _ _))
    right_inv _ := rfl }

def BranchFibers.constantFieldPoint (i : I) : Over.mk b ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I :=
  Over.homMk (b ≫ Sigma.ι (fun _ : I => S) i) (by
    change (b ≫ Sigma.ι (fun _ : I => S) i) ≫ Sigma.desc (fun _ : I => 𝟙 S) = b
    rw [Category.assoc, Sigma.ι_comp_desc, Category.comp_id])

theorem BranchFibers.constantFieldPointsEquiv_point (i : I) :
    BranchFibers.constantFieldPointsEquiv S I b (BranchFibers.constantFieldPoint S I b i) = i := by
  change AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S I ((b ≫ Sigma.ι (fun _ : I => S) i) default) = i
  exact AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i (b default)

theorem BranchFibers.constantFieldPointsEquiv_symm (i : I) :
    (BranchFibers.constantFieldPointsEquiv S I b).symm i = BranchFibers.constantFieldPoint S I b i :=
  (BranchFibers.constantFieldPointsEquiv S I b).symm_apply_eq.mpr (BranchFibers.constantFieldPointsEquiv_point S I b i).symm

end ConstantPoints

variable {B : Scheme.{0}} {X : Over B} (C : Correspondences.EtaleCorrespondence X)
  {T T' : Over B} (x : T ⟶ X) (a : T' ⟶ T)

/-- Pullback sections over an arbitrary map into the test scheme are
exactly the branches of the composed test point. -/
def Correspondences.EtaleCorrespondence.relativeFiberSectionEquiv : C.Fiber (a ≫ x) ≃
    (Over.mk a.left ⟶ Over.mk (pullback.snd C.source.left x.left)) where
  toFun c := Over.homMk (pullback.lift c.val.left a.left (by
    exact congrArg (fun z => z.left) c.property)) (pullback.lift_snd _ _ _)
  invFun p := ⟨Over.homMk (p.left ≫ pullback.fst C.source.left x.left) (by
    have hp : p.left ≫ pullback.snd C.source.left x.left = a.left := p.w
    calc
      _ = p.left ≫ pullback.fst C.source.left x.left ≫ C.source.left ≫ X.hom := by
        rw [C.source.w]
        simp only [Category.assoc]
      _ = p.left ≫ pullback.snd C.source.left x.left ≫ x.left ≫ X.hom := by
        rw [← Category.assoc (pullback.fst C.source.left x.left), pullback.condition]
        simp only [Category.assoc]
      _ = T'.hom := by rw [← Category.assoc p.left, hp, x.w, a.w]), by
    have hp : p.left ≫ pullback.snd C.source.left x.left = a.left := p.w
    apply Over.OverMorphism.ext
    change (p.left ≫ pullback.fst C.source.left x.left) ≫ C.source.left = a.left ≫ x.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp]⟩
  left_inv c := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  right_inv p := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans p.w.symm

variable {k : Type} [Field k] {b : Spec (.of k) ⟶ B}

/-- The labels of a splitting are in bijection with all actual geometric
branches after any field-valued base change of its test scheme. -/
def Correspondences.EtaleCorrespondence.splitFiberEquiv (a : Over.mk b ⟶ T) {n : ℕ} (e : C.BranchSplitting x n) :
    Fin n ≃ C.Fiber (a ≫ x) :=
  (BranchFibers.constantFieldPointsEquiv T.left (Fin n) a.left).symm.trans
    ((Iso.homCongr (Iso.refl _)
      ((TateComparison.BranchSplitting.constantCoproductIso T.left (Fin n)).symm ≪≫ e)).trans
        (C.relativeFiberSectionEquiv x a).symm)

theorem Correspondences.EtaleCorrespondence.splitFiberEquiv_val (a : Over.mk b ⟶ T) {n : ℕ}
    (e : C.BranchSplitting x n) (i : Fin n) :
    (C.splitFiberEquiv x a e i).val = a ≫ (C.splitBranch x e i).val := by
  simp only [Correspondences.EtaleCorrespondence.splitFiberEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Iso.trans_hom, Iso.symm_hom, BranchFibers.constantFieldPointsEquiv_symm]
  apply Over.OverMorphism.ext
  change (((a.left ≫ Sigma.ι (fun _ : Fin n => T.left) i) ≫
    (Sigma.desc (fun j : Fin n => (Sigma.ι (fun _ : Fin n => Over.mk (𝟙 T.left)) j).left)) ≫ e.hom.left) ≫
      pullback.fst C.source.left x.left) =
    a.left ≫ ((Sigma.ι (fun _ : Fin n => Over.mk (𝟙 T.left)) i).left ≫ e.hom.left) ≫
      pullback.fst C.source.left x.left
  simp only [Category.assoc, Sigma.ι_comp_desc_assoc]

theorem Correspondences.EtaleCorrespondence.splitFiberEquiv_endpoint (a : Over.mk b ⟶ T) {n : ℕ}
    (e : C.BranchSplitting x n) (i : Fin n) :
    C.endpoint (C.splitFiberEquiv x a e i) = a ≫ C.endpoint (C.splitBranch x e i) := by
  rw [Correspondences.EtaleCorrespondence.endpoint, Correspondences.EtaleCorrespondence.splitFiberEquiv_val, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
