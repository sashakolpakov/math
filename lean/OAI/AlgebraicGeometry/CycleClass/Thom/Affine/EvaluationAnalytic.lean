import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineMaps

/-! # Evaluation Analytic -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.EvaluationAnalytic.Constructions

noncomputable section

/-! Analyticity into a smooth affine point manifold is detected by its actual regular-function evaluations. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineMaps
open scoped _root_.Manifold ContDiff

variable {A M E : Type} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.Smooth ℂ A]
  [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M]

theorem contMDiff_affine_of_eval (u : M → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hc : Continuous u)
    (hu : ∀ a : A, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun x => u x a)) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) ω u := by
  apply contMDiff_iff.mpr
  refine ⟨hc, ?_⟩
  intro x y
  let e := chartAt E x
  let f := chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) y
  have heval (a : A) : ContDiffOn ℂ ω (fun z => u (e.symm z) a) e.target := by
    have ht := (contMDiff_iff.mp (hu a)).2 x (0 : ℂ)
    simpa only [e, extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
      extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      chartAt_self_eq, OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_source,
      Function.comp_id, Function.id_comp, Function.comp_def, Set.preimage_id,
      Set.range_id, Set.inter_univ, Set.preimage_univ, id_eq, Set.preimage,
      Set.mem_ofPred_eq, Set.ofPred_mem_eq, Set.mem_univ, Set.ofPred_true] using ht
  have hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) :=
    chart_mem_atlas _ y
  obtain ⟨g, hg, hcoords⟩ := hf.2
  have ht : ContDiffOn ℂ ω (fun z => f (u (e.symm z)))
      (e.target ∩ {z | u (e.symm z) ∈ f.source}) := by
    apply contDiffOn_pi.mpr
    intro j
    obtain ⟨a, k, hcoord⟩ := hcoords j
    have hval (b : A) : ContDiffOn ℂ ω (fun z => u (e.symm z) b)
        (e.target ∩ {z | u (e.symm z) ∈ f.source}) :=
      (heval b).mono Set.inter_subset_left
    apply ((hval a).div ((hval g).pow k) (fun z hz => pow_ne_zero k (hg _ hz.2))).congr
    intro z hz
    exact hcoord _ hz.2
  simpa only [e, f, extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq] using ht

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.EvaluationAnalytic.Constructions
