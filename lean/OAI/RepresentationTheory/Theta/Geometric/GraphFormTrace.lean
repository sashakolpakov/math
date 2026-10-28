import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches

/-! # Graph Form Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric.GraphFormTrace

noncomputable section

/-! A graph correspondence has exactly one branch on every affine
test, so its algebraic trace is the actual pullback by the graph map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches

def singletonCoproductIso (S : Scheme.{0}) :
    (∐ fun _ : Fin 1 => Over.mk (𝟙 S)) ≅ Over.mk (𝟙 S) where
  hom := Sigma.desc (fun _ => 𝟙 _)
  inv := Sigma.ι (fun _ : Fin 1 => Over.mk (𝟙 S)) 0
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [Sigma.ι_comp_desc_assoc, Category.id_comp, Category.comp_id]
  inv_hom_id := Sigma.ι_comp_desc _ _

def graphBranchSplitting {Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Z)
    [IsIso C.source.left] {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (t : T ⟶ Z) : C.BranchSplitting t 1 :=
  singletonCoproductIso T.left ≪≫
    Over.isoMk (asIso (pullback.snd C.source.left t.left)).symm (by
      change inv (pullback.snd C.source.left t.left) ≫ pullback.snd C.source.left t.left = 𝟙 _
      exact IsIso.inv_hom_id _)

theorem branchTrace_graph_pullback {Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Z)
    [IsIso C.source.left] (τ : Z ⟶ Z) (hτ : C.target = C.source ≫ τ)
    (form other : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms Z) (htrace : AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace C form other) :
    other = AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback τ form := by
  apply Subtype.ext
  funext R t
  let e := graphBranchSplitting C t
  have he : C.endpoint (C.splitBranch t e 0) = t ≫ τ := by
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence.endpoint, hτ, ← Category.assoc, (C.splitBranch t e 0).property]
  exact (htrace R t 1 e).trans (by rw [Fin.sum_univ_one, he]; rfl)

end

end OAI.RepresentationTheory.Theta.Geometric.GraphFormTrace
