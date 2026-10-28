import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeSplitting

/-! # Branch Splitting -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The finite-etale splitting theorem supplies actual branch
presentations in the TateComparison interface, over neighborhoods covering the source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

section ConstantCoproduct

universe u
variable (S : Scheme.{u}) (I : Type u)

def BranchSplitting.constantCoproductInclusion (i : I) :
    Over.mk (𝟙 S) ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I :=
  Over.homMk (Sigma.ι (fun _ : I => S) i) (Sigma.ι_comp_desc _ _)

/-- The scheme coproduct used by HilbertConstruction and the coproduct in the slice
used for TateComparison branches are canonically isomorphic. -/
def BranchSplitting.constantCoproductIso :
    (∐ fun _ : I => Over.mk (𝟙 S)) ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I where
  hom := Sigma.desc (TateComparison.BranchSplitting.constantCoproductInclusion S I)
  inv := Over.homMk
    (Sigma.desc (fun i : I => (Sigma.ι (fun _ : I => Over.mk (𝟙 S)) i).left)) (by
      change (Sigma.desc (fun i : I => (Sigma.ι (fun _ : I => Over.mk (𝟙 S)) i).left)) ≫
        (∐ fun _ : I => Over.mk (𝟙 S)).hom = Sigma.desc (fun _ : I => 𝟙 S)
      apply Sigma.hom_ext
      intro i
      rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
      exact (Sigma.ι (fun _ : I => Over.mk (𝟙 S)) i).w)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc, Category.comp_id]
    apply Over.OverMorphism.ext
    exact Sigma.ι_comp_desc _ i
  inv_hom_id := by
    apply Over.OverMorphism.ext
    change (Sigma.desc (fun i : I => (Sigma.ι (fun _ : I => Over.mk (𝟙 S)) i).left)) ≫
      (Sigma.desc (TateComparison.BranchSplitting.constantCoproductInclusion S I)).left = 𝟙 (∐ fun _ : I => S)
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_comp_desc]
    have h := congrArg (fun f => f.left)
      (Sigma.ι_comp_desc (TateComparison.BranchSplitting.constantCoproductInclusion S I) i)
    exact h.trans (Category.comp_id _).symm

theorem BranchSplitting.constantCoproductIso_ι_hom (i : I) :
    Sigma.ι (fun _ : I => Over.mk (𝟙 S)) i ≫ (TateComparison.BranchSplitting.constantCoproductIso S I).hom =
      TateComparison.BranchSplitting.constantCoproductInclusion S I i := Sigma.ι_comp_desc _ _

theorem BranchSplitting.constantCoproductInclusion_inv (i : I) :
    TateComparison.BranchSplitting.constantCoproductInclusion S I i ≫ (TateComparison.BranchSplitting.constantCoproductIso S I).inv =
      Sigma.ι (fun _ : I => Over.mk (𝟙 S)) i := by
  rw [← TateComparison.BranchSplitting.constantCoproductIso_ι_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end ConstantCoproduct

variable {B : Scheme.{0}} {X : Over B} (C : Correspondences.EtaleCorrespondence X)

/-- Every source point lies under an actual etale neighborhood whose
pulled-back cover splits into finitely many branches. -/
theorem Correspondences.EtaleCorrespondence.exists_branch_splitting_at (z : X.left) :
    ∃ (T : Scheme) (u : T ⟶ X.left), Etale u ∧ z ∈ Set.range u ∧
      ∃ n : ℕ, Nonempty (C.BranchSplitting
        (Over.homMk u rfl : Over.mk (u ≫ X.hom) ⟶ X) n) := by
  let Y : Over X.left := Over.mk C.source.left
  have : IsFinite Y.hom := C.finite
  have : Etale Y.hom := C.etale
  obtain ⟨R, _, u, hu, hz, n, ⟨e⟩⟩ :=
    AbelianModuli.ReferenceFamily.SchemeSplitting.EtaleSplitting.exists_scheme_splitting_at Y z
  refine ⟨Spec (.of R), u, hu, hz, n, ⟨?_⟩⟩
  exact TateComparison.BranchSplitting.constantCoproductIso (Spec (.of R)) (Fin n) ≪≫ e

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
