import OAI.AlgebraicGeometry.Comparison.Betti.Open.IntrinsicPurity
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRhamComplex
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.PresheafInclusion
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Local Descent -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalDescent

noncomputable section

section

/-! An actual smooth form whose restrictions are holomorphic is holomorphic. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def ambientHolomorphicInclusion (U : Opens M) (n : ℕ) :
    DeRhamComplex.forms E U n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm.toLinearMap.comp (DeRhamComplex.inclusion E U n)

theorem ambientHolomorphicInclusion_restrict {U V : Opens M} (h : V ≤ U) (n : ℕ)
    (a : DeRhamComplex.forms E U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (ambientHolomorphicInclusion U n a) =
      ambientHolomorphicInclusion V n
        (HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n a) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V n).injective
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h
    ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm (DeRhamComplex.inclusion E U n a))) =
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V n ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V n).symm
      (DeRhamComplex.inclusion E V n (HolomorphicPullback.pullback (Opens.inclusion h)
        (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n a)))
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, HolomorphicPullback.pullback_inclusion]

theorem exists_holomorphic_of_cover {ι : Type} {U : Opens M} (V : ι → Opens M)
    (hsub : ∀ i, V i ≤ U) (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M)) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (b : ∀ i, DeRhamComplex.forms E (V i) n)
    (hb : ∀ i, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (V i) n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hsub i) a) =
      DeRhamComplex.inclusion E (V i) n (b i)) :
    ∃ c : DeRhamComplex.forms E U n, DeRhamComplex.inclusion E U n c = Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a := by
  have hp : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U n 0 (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a).val := by
    apply Open.IntrinsicPurity.Holomorphic.intrinsic_pure_of_cover_restrict_pure (p := n) (q := 0) V hsub hcover a
    intro i
    change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E (V i) n 0
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (V i) n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hsub i) a)).val
    rw [hb i]
    exact (b i).val.hasManifoldBidegree
  have hd : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U (n + 1) 0
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a)).val := by
    apply Open.IntrinsicPurity.Holomorphic.intrinsic_pure_of_cover_restrict_pure (p := n + 1) (q := 0) V hsub hcover
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a)
    intro i
    change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E (V i) (n + 1) 0
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (V i) (n + 1)
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hsub i) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a))).val
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d, ← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, hb i]
    exact DeRhamComplex.derivative_pure n (b i)
  let ap : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E U n 0 := ⟨Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a, hp⟩
  have hap : ap ∈ DeRhamComplex.forms E U n := by
    apply (DeRhamComplex.mem_forms_iff_derivative_pure n ap).mpr
    change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U (n + 1) 0
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a)).val
    rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d]
    exact hd
  exact ⟨⟨ap, hap⟩, rfl⟩

end

/-! The original actual holomorphic form presheaf is a sheaf on every complex manifold. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem existsUnique_holomorphicForm_glue (n : ℕ) {ι : Type} (U : ι → Opens M)
    (a : ∀ i, DeRhamComplex.forms E (U i) n)
    (ha : ∀ i j, HolomorphicPullback.pullback (Opens.inclusion (show U i ⊓ U j ≤ U i from inf_le_left))
      (contMDiff_inclusion (I := 𝓘(ℂ, E)) inf_le_left) n (a i) =
        HolomorphicPullback.pullback (Opens.inclusion (show U i ⊓ U j ≤ U j from inf_le_right))
          (contMDiff_inclusion (I := 𝓘(ℂ, E)) inf_le_right) n (a j)) :
    ∃! b : DeRhamComplex.forms E ↥(iSup U) n, ∀ i,
      HolomorphicPullback.pullback (Opens.inclusion (le_iSup U i))
        (contMDiff_inclusion (I := 𝓘(ℂ, E)) (le_iSup U i)) n b = a i := by
  let A : ∀ i, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (U i) n := fun i => ambientHolomorphicInclusion (U i) n (a i)
  have hA : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.Compatible A := by
    apply (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.compatible_iff_restrict A).mpr
    intro i j
    change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left (ambientHolomorphicInclusion (U i) n (a i)) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (ambientHolomorphicInclusion (U j) n (a j))
    rw [ambientHolomorphicInclusion_restrict, ambientHolomorphicInclusion_restrict]
    exact congrArg (ambientHolomorphicInclusion (U i ⊓ U j) n) (ha i j)
  obtain ⟨g, hg, huniq⟩ := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.existsUnique_glue_iSup A hA
  have hcover : ((iSup U : Opens M) : Set M) ⊆ ⋃ i, (U i : Set M) := by
    rw [Opens.coe_iSup]
  obtain ⟨b, hb⟩ := exists_holomorphic_of_cover U (fun i => le_iSup U i) hcover n g a (by
    intro i
    rw [hg i]
    exact (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (U i) n).apply_symm_apply (DeRhamComplex.inclusion E (U i) n (a i)))
  refine ⟨b, ?_, ?_⟩
  · intro i
    apply HolomorphicPullback.inclusion_injective n
    rw [HolomorphicPullback.pullback_inclusion, hb, ← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict, hg i]
    exact (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (U i) n).apply_symm_apply (DeRhamComplex.inclusion E (U i) n (a i))
  · intro c hc
    apply HolomorphicPullback.inclusion_injective n
    apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (iSup U) n).symm.injective
    rw [hb, LinearEquiv.symm_apply_apply]
    change ambientHolomorphicInclusion (iSup U) n c = g
    apply huniq
    intro i
    rw [ambientHolomorphicInclusion_restrict]
    exact congrArg (ambientHolomorphicInclusion (U i) n) (hc i)

theorem holomorphicPresheaf_isSheaf (n : ℕ) :
    TopCat.Presheaf.IsSheaf (X := TopCat.of M) ((Holomorphic.Presheaf.presheafComplex E M).X n) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := TopCat.of M)
    ((Holomorphic.Presheaf.presheafComplex E M).X n)).mpr
  intro ι U a ha
  exact existsUnique_holomorphicForm_glue E M n U a ha

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalDescent
