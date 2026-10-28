import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafPartition
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocalSumIdentity
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ExactLocalLift

/-! # Godement Global Exactness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.GodementGlobalExactness

noncomputable section

/-! On a compact smooth manifold, actual global sections of the Godement
resolution of each smooth form sheaf are exact in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

theorem smoothFormGodement_global_lift (p n : ℕ)
    (z : ((Godement.Resolution.godementComplex (TopCat.of M) (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p)).X (n + 1)).obj.obj (op ⊤))
    (hz : ((Godement.Resolution.godementComplex (TopCat.of M) (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p)).d
      (n + 1) (n + 2)).hom.app (op ⊤) z = 0) :
    ∃ t : ((Godement.Resolution.godementComplex (TopCat.of M) (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p)).X n).obj.obj (op ⊤),
      ((Godement.Resolution.godementComplex (TopCat.of M) (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p)).d n (n + 1)).hom.app (op ⊤) t = z := by
  classical
  let F := Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M p
  let K := Godement.Resolution.godementComplex (TopCat.of M) F
  let S := K.sc' n (n + 1) (n + 2)
  have hS : S.Exact := (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mp
    (Godement.Resolution.godementComplex_exactAt_succ (TopCat.of M) F n)
  have hlocal (x : M) : ∃ U : Opens M, x ∈ U ∧
      ∃ a : (K.X n).obj.obj (op U), (K.d n (n + 1)).hom.app (op U) a =
        (K.X (n + 1)).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op z := by
    obtain ⟨U, hU, hxU, a, ha⟩ := Sheaf.ExactLocalLift.Godement.local_section_lift_of_exact S hS ⊤ z hz ⟨x, trivial⟩
    exact ⟨U, hxU, a, ha⟩
  choose U hx a ha using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set M))
    (fun x => (U x).isOpen) (by intro x _; exact mem_iUnion.mpr ⟨x, hx x⟩)
  have hcover : ∀ x : M, ∃ i : s, x ∈ U i.val := by
    intro x
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨V, f, hc, hf, hsum⟩ := SheafPartition.Godement.exists_smoothFormSheaf_partition E M (fun i : s => U i.val) hcover p
  exact Godement.LocalSumIdentity.godement_finite_partition_lift (F := F) (fun i : s => U i.val) V hc f hf hsum n z
    (fun i => a i.val) (fun i => ha i.val)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.GodementGlobalExactness
