import OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocallyFinitePatch
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ExactLocalLift

/-! # Restricted Smooth Godement Exactness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothGodementExactness

noncomputable section

/-! The Godement resolution of the literal restricted smooth form sheaf has exact global sections on every sigma-compact open submanifold. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem restrictedSmoothFormGodement_global_lift (O : Opens M) [SigmaCompactSpace O] (p n : ℕ)
    (z : ((Godement.Resolution.godementComplex (TopCat.of O) (RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p)).X (n + 1)).obj.obj (op ⊤))
    (hz : ((Godement.Resolution.godementComplex (TopCat.of O) (RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p)).d
      (n + 1) (n + 2)).hom.app (op ⊤) z = 0) :
    ∃ t : ((Godement.Resolution.godementComplex (TopCat.of O) (RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p)).X n).obj.obj (op ⊤),
      ((Godement.Resolution.godementComplex (TopCat.of O) (RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p)).d n (n + 1)).hom.app (op ⊤) t = z := by
  classical
  let F := RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p
  let K := Godement.Resolution.godementComplex (TopCat.of O) F
  let S := K.sc' n (n + 1) (n + 2)
  have hS : S.Exact := (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mp
    (Godement.Resolution.godementComplex_exactAt_succ (TopCat.of O) F n)
  have hlocal (x : O) : ∃ U : Opens O, x ∈ U ∧
      ∃ a : (K.X n).obj.obj (op U), (K.d n (n + 1)).hom.app (op U) a =
        (K.X (n + 1)).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op z := by
    obtain ⟨U, hU, hxU, a, ha⟩ := Sheaf.ExactLocalLift.Godement.local_section_lift_of_exact S hS ⊤ z hz ⟨x, trivial⟩
    exact ⟨U, hxU, a, ha⟩
  choose U hx a ha using hlocal
  obtain ⟨V, f, hc, hf, hsum⟩ := RestrictedSmoothSheaf.Godement.exists_restrictedSmoothFormSheaf_locally_finite_partition
    (E := E) O U (fun x => ⟨x, hx x⟩) p
  exact Godement.LocallyFinitePatch.godement_locally_finite_partition_lift (F := F) U V hc f hf hsum n z a ha

theorem restrictedSmoothFormGodement_sections_exactAt_succ (O : Opens M) [SigmaCompactSpace O]
    (p n : ℕ) :
    (((FlasqueBiproduct.sections (⊤ : Opens O)).mapHomologicalComplex (.up ℕ)).obj
      (Godement.Resolution.godementComplex (TopCat.of O) (RestrictedSmoothSheaf.Godement.restrictedSmoothFormSheaf E M O p))).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  exact restrictedSmoothFormGodement_global_lift O p n

end

end OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothGodementExactness
