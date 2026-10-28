import OAI.AlgebraicGeometry.Comparison.Betti.Open.FiltrationDescent
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf

/-! # Global Filtered Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GlobalFilteredSections.Hodge

noncomputable section

/-! Global sections of the filtered sheaf are exactly the original
globally filtered smooth forms, including their actual exterior differential. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem onTop_intrinsic_pure_iff (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (⊤ : Opens M) n (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a) ∈
      ManifoldFormFiltration.Hodge.pureFormsInDegree E (⊤ : Opens M) n i ↔ a ∈ ManifoldFormFiltration.Hodge.pureFormsInDegree E M n i := by
  rcases i with ⟨⟨p, q⟩, hi⟩
  subst n
  change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E (⊤ : Opens M) p q
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (⊤ : Opens M) (p + q) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a)).val ↔ _
  rw [Open.IntrinsicPurity.Holomorphic.intrinsicOpenFormEquiv_pure_iff]
  have he : (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a).extension = a.val :=
    congrArg Subtype.val (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.toGlobal_onOpen a)
  rw [he]
  change (∀ e ∈ atlas E M, ∀ y ∈ e.target, e.symm y ∈ (⊤ : Opens M) →
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (a.val.inChart e y)) ↔ Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q a.val
  simp only [Opens.mem_top, forall_true_left]
  rfl

theorem onTop_mem_openFormFiltration (n : ℕ) (r : ℤ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : a ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a ∈ Open.FiltrationDescent.Hodge.openFormFiltration (⊤ : Opens M) n r := by
  have h : ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r ≤
      (Open.FiltrationDescent.Hodge.openFormFiltration (⊤ : Opens M) n r).comap (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤) := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro b hb
    change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (⊤ : Opens M) n (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ b) ∈
      ManifoldFormFiltration.Hodge.manifoldFormFiltration E (⊤ : Opens M) n r
    apply Submodule.mem_iSup_of_mem i
    apply Submodule.mem_iSup_of_mem hi
    exact (onTop_intrinsic_pure_iff E M n i b).mpr hb
  exact h ha

theorem toGlobal_mem_manifoldFormFiltration (n : ℕ) (r : ℤ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) n) (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration (⊤ : Opens M) n r) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal a ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r := by
  let L := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal.comp (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (⊤ : Opens M) n).symm.toLinearMap
  have h : ManifoldFormFiltration.Hodge.manifoldFormFiltration E (⊤ : Opens M) n r ≤
      (ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r).comap L := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro b hb
    apply Submodule.mem_iSup_of_mem i
    apply Submodule.mem_iSup_of_mem hi
    apply (onTop_intrinsic_pure_iff E M n i (L b)).mp
    change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (⊤ : Opens M) n
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal
        ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (⊤ : Opens M) n).symm b))) ∈ _
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.onOpen_toGlobal, LinearEquiv.apply_symm_apply]
    exact hb
  have hh := h ha
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal
    ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (⊤ : Opens M) n).symm
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (⊤ : Opens M) n a)) ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r at hh
  rwa [LinearEquiv.symm_apply_apply] at hh

def globalFilteredSectionsEquiv (n : ℕ) (r : ℤ) :
    Open.FiltrationDescent.Hodge.openFormFiltration (E := E) (⊤ : Opens M) n r ≃ₗ[ℂ] ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r where
  toFun a := ⟨Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal a.val, toGlobal_mem_manifoldFormFiltration E M n r a.val a.property⟩
  invFun a := ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a.val, onTop_mem_openFormFiltration E M n r a.val a.property⟩
  left_inv a := Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.onOpen_toGlobal a.val)
  right_inv a := Subtype.ext (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.toGlobal_onOpen a.val)
  map_add' a b := Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal.map_add a.val b.val)
  map_smul' c a := Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal.map_smul c a.val)

end

end OAI.AlgebraicGeometry.Comparison.Betti.GlobalFilteredSections.Hodge
