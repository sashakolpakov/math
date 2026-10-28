import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.LocalPartition
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocallyFinitePatch
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ExactLocalLift

/-! # Sigma Compact Godement Exactness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactGodementExactness

noncomputable section

/-! On a sigma-compact smooth manifold, actual global sections of the Godement
resolution of each smooth form sheaf are exact in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem sigmaCompact_smoothFormGodement_global_lift (p n : ℕ)
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
  obtain ⟨V, f, hc, hf, hsum⟩ := Smooth.LocalPartition.Godement.exists_smoothFormSheaf_locally_finite_partition
    E M U (fun x => ⟨x, hx x⟩) p
  exact Godement.LocallyFinitePatch.godement_locally_finite_partition_lift (F := F) U V hc f hf hsum n z a ha

end

end OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactGodementExactness
