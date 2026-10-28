import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFilteredDifferential
import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFilteredPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Open.IntrinsicPurity
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf

/-! # Filtration Descent -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.FiltrationDescent.Hodge

noncomputable section

section

/-! The smooth Hodge filtration on actual ambient open sections. It is
preserved by restrictions and the actual exterior differential. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def openFormFiltration (U : Opens M) (n : ℕ) (r : ℤ) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :=
  (ManifoldFormFiltration.Hodge.manifoldFormFiltration E U n r).comap (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).toLinearMap

def openTypeProjection (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) :
    Module.End ℂ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm.toLinearMap.comp
    ((ManifoldFormFiltration.Hodge.manifoldTypeProjection E U n i).comp (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).toLinearMap)

theorem openFormFiltration_restrict {U V : Opens M} (h : V ≤ U) (n : ℕ) (r : ℤ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ openFormFiltration U n r) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a ∈ openFormFiltration V n r := by
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) ∈
    ManifoldFormFiltration.Hodge.manifoldFormFiltration E V n r
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict]
  exact ManifoldFilteredPullback.Hodge.manifoldFormFiltration_pullback (Opens.inclusion h)
    (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n r (Submodule.mem_map_of_mem ha)

theorem openFormFiltration_d {U : Opens M} (n : ℕ) (r : ℤ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ openFormFiltration U n r) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a ∈ openFormFiltration U (n + 1) r := by
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a) ∈
    ManifoldFormFiltration.Hodge.manifoldFormFiltration E U (n + 1) r
  rw [← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d]
  exact ManifoldFilteredDifferential.Hodge.manifoldExteriorDerivative_filtered E U n r (Submodule.mem_map_of_mem ha)

theorem openTypeProjection_restrict [FiniteDimensional ℝ E]
    {U V : Opens M} (h : V ≤ U) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (openTypeProjection U n i a) =
      openTypeProjection V n i (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V n).injective
  simp only [openTypeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict, LinearEquiv.apply_symm_apply]
  exact ManifoldFilteredPullback.Hodge.manifoldTypeProjection_pullback (Opens.inclusion h)
    (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n i (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a)

theorem mem_openFormFiltration_iff_projections [FiniteDimensional ℝ E]
    (U : Opens M) (n : ℕ) (r : ℤ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    a ∈ openFormFiltration U n r ↔
      ∀ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n, (i.val.1 : ℤ) < r → openTypeProjection U n i a = 0 := by
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration E U n r ↔ _
  rw [ManifoldFormFiltration.Hodge.mem_manifoldFormFiltration_iff_projections]
  simp only [openTypeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    EmbeddingLike.map_eq_zero_iff]

end

/-! Membership in the actual smooth Hodge filtration is local, and
compatible filtered sections glue uniquely to an actual filtered section. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem openFormFiltration_of_cover {ι : Type} {U : Opens M} (V : ι → Opens M)
    (hsub : ∀ i, V i ≤ U) (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (n : ℕ) (r : ℤ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (ha : ∀ i, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hsub i) a ∈ openFormFiltration (V i) n r) :
    a ∈ openFormFiltration U n r := by
  rw [mem_openFormFiltration_iff_projections]
  intro j hj
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover x.property)
  have hp := (mem_openFormFiltration_iff_projections (V i) n r
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hsub i) a)).mp (ha i) j hj
  have hzero : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hsub i) (openTypeProjection U n j a) = 0 :=
    (openTypeProjection_restrict (hsub i) n j a).trans hp
  exact congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (V i) n => b ⟨x.val, hi⟩) hzero

theorem existsUnique_filteredForm_glue {ι : Type} (U : ι → Opens M) (n : ℕ) (r : ℤ)
    (a : ∀ i, openFormFiltration (E := E) (U i) n r)
    (ha : ∀ i j, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show U i ⊓ U j ≤ U i from inf_le_left)
        (a i).val =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show U i ⊓ U j ≤ U j from inf_le_right) (a j).val) :
    ∃! b : openFormFiltration (E := E) (iSup U) n r,
      ∀ i, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (le_iSup U i) b.val = (a i).val := by
  have hA : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.Compatible (fun i => (a i).val) :=
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.compatible_iff_restrict _).mpr ha
  obtain ⟨g, hg, huniq⟩ := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.existsUnique_glue_iSup (fun i => (a i).val) hA
  have hcover : ((iSup U : Opens M) : Set M) ⊆ ⋃ i, (U i : Set M) := by
    rw [Opens.coe_iSup]
  have hfiltered : g ∈ openFormFiltration (iSup U) n r :=
    openFormFiltration_of_cover U (fun i => le_iSup U i) hcover n r g (by
      intro i
      rw [hg i]
      exact (a i).property)
  refine ⟨⟨g, hfiltered⟩, hg, ?_⟩
  intro b hb
  exact Subtype.ext (huniq b.val hb)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.FiltrationDescent.Hodge
