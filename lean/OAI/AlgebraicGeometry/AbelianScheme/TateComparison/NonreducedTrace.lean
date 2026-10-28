import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConstantPermutations
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LocalTrace

/-! # Nonreduced Trace -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Branch sums are independent of the splitting on every test scheme.
The proof uses open sets on which the actual sheet permutation is fixed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {B : Scheme.{0}} {X A : Over B} [GrpObj A] [IsCommMonObj A]
  (C : Correspondences.EtaleCorrespondence X) {T : Over B} (x : T ⟶ X)

def Correspondences.EtaleCorrespondence.splitConstantIso {n : ℕ} (e : C.BranchSplitting x n) :
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme T.left (Fin n) ≅ Over.mk (pullback.snd C.source.left x.left) :=
  (TateComparison.BranchSplitting.constantCoproductIso T.left (Fin n)).symm ≪≫ e

theorem Correspondences.EtaleCorrespondence.splitBranch_constant {n : ℕ} (e : C.BranchSplitting x n) (i : Fin n) :
    (C.splitBranch x e i).val.left = Sigma.ι (fun _ : Fin n => T.left) i ≫
      (C.splitConstantIso x e).hom.left ≫ pullback.fst C.source.left x.left := by
  have h := congrArg (fun f => f.left)
    (TateComparison.BranchSplitting.constantCoproductInclusion_inv T.left (Fin n) i)
  change (Sigma.ι (fun _ : Fin n => T.left) i ≫ (TateComparison.BranchSplitting.constantCoproductIso T.left (Fin n)).inv.left) =
    (Sigma.ι (fun _ : Fin n => Over.mk (𝟙 T.left)) i).left at h
  simp only [Correspondences.EtaleCorrespondence.splitBranch, Correspondences.EtaleCorrespondence.branchOfSection, Over.homMk_left, Over.comp_left,
    Correspondences.EtaleCorrespondence.splitConstantIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← h]
  simp only [AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme, Category.assoc]

theorem Correspondences.EtaleCorrespondence.splitBranch_permutation_restrict {n m : ℕ}
    (e : C.BranchSplitting x n) (e' : C.BranchSplitting x m)
    (p : Fin n ≃ Fin m) (i : Fin n) :
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber
      (ConstantPermutations.constantIsoPermutation (C.splitConstantIso x e ≪≫ (C.splitConstantIso x e').symm)) p).ι ≫
        (C.splitBranch x e i).val.left =
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber
      (ConstantPermutations.constantIsoPermutation (C.splitConstantIso x e ≪≫ (C.splitConstantIso x e').symm)) p).ι ≫
        (C.splitBranch x e' (p i)).val.left := by
  have hp := ConstantPermutations.constantIsoPermutation_restrict
    (C.splitConstantIso x e ≪≫ (C.splitConstantIso x e').symm) p i
  let U := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber
    (ConstantPermutations.constantIsoPermutation (C.splitConstantIso x e ≪≫ (C.splitConstantIso x e').symm)) p
  let j : Over.mk U.ι ⟶ Over.mk (𝟙 T.left) := Over.homMk U.ι (Category.comp_id _)
  have hp' : j ≫ TateComparison.BranchSplitting.constantCoproductInclusion T.left (Fin n) i ≫
        (C.splitConstantIso x e ≪≫ (C.splitConstantIso x e').symm).hom =
      j ≫ TateComparison.BranchSplitting.constantCoproductInclusion T.left (Fin m) (p i) := Over.OverMorphism.ext hp
  have h := congrArg (fun f => f ≫ (C.splitConstantIso x e').hom) hp'
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  have h := congrArg (fun f => f.left ≫ pullback.fst C.source.left x.left) h
  change (U.ι ≫ Sigma.ι (fun _ : Fin n => T.left) i ≫ (C.splitConstantIso x e).hom.left) ≫ _ =
    (U.ι ≫ Sigma.ι (fun _ : Fin m => T.left) (p i) ≫ (C.splitConstantIso x e').hom.left) ≫ _ at h
  simpa only [U, Correspondences.EtaleCorrespondence.splitBranch_constant, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme, Category.assoc] using h

/-- The local algebraic trace is independent of the chosen splitting,
including when the test scheme has nilpotents. -/
theorem Correspondences.EtaleCorrespondence.localTraceMap_independent_all (f : X ⟶ A) {n m : ℕ}
    (e : C.BranchSplitting x n) (e' : C.BranchSplitting x m) :
    C.localTraceMap f x e = C.localTraceMap f x e' := by
  let c := ConstantPermutations.constantIsoPermutation (C.splitConstantIso x e ≪≫ (C.splitConstantIso x e').symm)
  apply Over.OverMorphism.ext
  apply (cancel_epi (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso c).hom).mp
  apply Sigma.hom_ext
  intro p
  rw [AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc]
  let U : Over B := Over.mk ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c p).ι ≫ T.hom)
  let j : U ⟶ T := Over.homMk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c p).ι rfl
  have hp (i : Fin n) :
      j ≫ C.endpoint (C.splitBranch x e i) ≫ f =
      j ≫ C.endpoint (C.splitBranch x e' (p i)) ≫ f := by
    apply Over.OverMorphism.ext
    change (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c p).ι ≫ (C.splitBranch x e i).val.left ≫ C.target.left ≫ f.left = _
    rw [← Category.assoc, C.splitBranch_permutation_restrict x e e' p i]
    rfl
  have h : j ≫ C.localTraceMap f x e = j ≫ C.localTraceMap f x e' := by
    change Correspondences.EtaleCorrespondence.precompPointHom j (∏ i : Fin n, C.endpoint (C.splitBranch x e i) ≫ f) =
      Correspondences.EtaleCorrespondence.precompPointHom j (∏ i : Fin m, C.endpoint (C.splitBranch x e' i) ≫ f)
    rw [map_prod, map_prod]
    exact (Finset.prod_congr rfl (fun i _ => hp i)).trans
      (p.prod_comp (fun i => j ≫ C.endpoint (C.splitBranch x e' i) ≫ f))
  exact congrArg (fun f => f.left) h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
