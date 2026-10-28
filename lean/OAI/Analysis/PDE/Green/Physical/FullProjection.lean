import OAI.Analysis.PDE.Green.Physical.CellGeometry
import OAI.Analysis.PDE.Green.Physical.JointExtension
import OAI.Analysis.PDE.Green.ActualSmooth

/-! The exact physical complex coordinates as a surjective real-linear map
from all three-slot spacetime coordinates. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped Topology

def fullPhysicalProjection (d : ℕ) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 →L[ℝ] (ℂ × (Option (Fin d) → ℂ)) :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj ((0 : Fin (d + 2)), (1 : Fin 3))) +
    Complex.I • Complex.ofRealCLM.comp
      (EuclideanSpace.proj ((0 : Fin (d + 2)), (2 : Fin 3)))).prod
  (ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (EuclideanSpace.proj (((finSuccEquiv d).symm i).succ, (1 : Fin 3))) +
      Complex.I • Complex.ofRealCLM.comp
        (EuclideanSpace.proj (((finSuccEquiv d).symm i).succ, (2 : Fin 3))))

theorem fullPhysicalProjection_fiber (d : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    fullPhysicalProjection d (fiberEmbedding (d + 1) 3 z y) =
      (energyComplexTime z, physicalSpatialProjection d y) := by
  apply Prod.ext
  · change ((fiberEmbedding (d + 1) 3 z y (0, 1) : ℂ) +
        Complex.I * (fiberEmbedding (d + 1) 3 z y (0, 2) : ℂ)) = _
    simp [fiberEmbedding, timeInjection, spatialInjection, spatialInjectionLinear,
      energyComplexTime]
  · ext i
    change ((fiberEmbedding (d + 1) 3 z y (((finSuccEquiv d).symm i).succ, 1) : ℂ) +
      Complex.I * (fiberEmbedding (d + 1) 3 z y (((finSuccEquiv d).symm i).succ, 2) : ℂ)) = _
    simp [fiberEmbedding, timeInjection, spatialInjection, spatialInjectionLinear,
      physicalSpatialProjection_apply]

theorem fullPhysicalProjection_eq (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    fullPhysicalProjection d x =
      (energyComplexTime (timeSpaceEquiv (d + 1) 3 x).1,
        physicalSpatialProjection d (timeSpaceEquiv (d + 1) 3 x).2) := by
  have h := fullPhysicalProjection_fiber d (timeSpaceEquiv (d + 1) 3 x).1
    (timeSpaceEquiv (d + 1) 3 x).2
  simpa only [← timeSpaceEquiv_symm_apply, Prod.mk.eta,
    MeasurableEquiv.symm_apply_apply] using h

theorem fullPhysicalProjection_fst (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    (fullPhysicalProjection d x).1 = energyComplexTime (timeProjection (d + 1) 3 x) := by
  rw [fullPhysicalProjection_eq, timeSpaceEquiv_fst]

theorem fullPhysicalProjection_real_translation (d : ℕ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (i : Fin (d + 2)) :
    fullPhysicalProjection d (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (i, 0)) = fullPhysicalProjection d x := by
  rw [map_add]
  have hz : fullPhysicalProjection d (OAI.Analysis.PDE.Dirichlet.coordinateVector (i, 0)) = 0 := by
    apply Prod.ext
    · simp [fullPhysicalProjection, OAI.Analysis.PDE.Dirichlet.coordinateVector]
    · ext j
      simp [fullPhysicalProjection, OAI.Analysis.PDE.Dirichlet.coordinateVector]
  rw [hz, add_zero]

theorem fullPhysicalProjection_surjective (d : ℕ) :
    Function.Surjective (fullPhysicalProjection d) := by
  rintro ⟨τ, q⟩
  let z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 := WithLp.toLp 2 (fun p => ![(0 : ℝ), τ.re, τ.im] p.2)
  refine ⟨fiberEmbedding (d + 1) 3 z (physicalSpatialEmbedding d 0 q), ?_⟩
  rw [fullPhysicalProjection_fiber, physicalSpatialProjection_embedding]
  apply Prod.ext
  · change (τ.re : ℂ) + Complex.I * (τ.im : ℂ) = τ
    apply Complex.ext <;> simp
  · rfl

theorem fderiv_comp_surjective_ne_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Surjective L) {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (L x)) (hne : fderiv ℝ f (L x) ≠ 0) :
    fderiv ℝ (fun y => f (L y)) x ≠ 0 := by
  intro hz
  apply hne
  ext v
  obtain ⟨w, rfl⟩ := hL v
  have h := congrArg (fun D : E →L[ℝ] ℝ => D w)
    ((hf.hasFDerivAt.comp x L.hasFDerivAt).fderiv.symm.trans hz)
  simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h

theorem fullPhysical_extension_regular {d : ℕ}
    {R : (ℂ × (Option (Fin d) → ℂ)) → ℝ} (hR : ContDiff ℝ 1 R)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3}
    (hne : fderiv ℝ R (fullPhysicalProjection d x) ≠ 0) :
    fderiv ℝ (fun y => R (fullPhysicalProjection d y)) x ≠ 0 :=
  fderiv_comp_surjective_ne_zero (fullPhysicalProjection d)
    (fullPhysicalProjection_surjective d) (hR.differentiable (by norm_num) _) hne

theorem time_test_eventually_zero_of_notMem {d : ℕ}
    {T : Set ℂ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ}
    (hs : energyComplexTime '' tsupport η ⊆ T)
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3} (hx : (fullPhysicalProjection d x).1 ∉ T) :
    (fun y => η (timeProjection (d + 1) 3 y)) =ᶠ[𝓝 x] (fun _ => 0) := by
  have ht : timeProjection (d + 1) 3 x ∉ tsupport η := by
    intro h
    apply hx
    rw [fullPhysicalProjection_fst]
    exact hs (mem_image_of_mem energyComplexTime h)
  have hzero : η =ᶠ[𝓝 (timeProjection (d + 1) 3 x)] (fun _ => 0) := by
    have hU : IsOpen ((tsupport η)ᶜ) := isClosed_closure.isOpen_compl
    filter_upwards [hU.mem_nhds ht] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  exact hzero.comp_tendsto ((timeProjection (d + 1) 3).continuous.tendsto x)

theorem fullPhysical_extension_regular_or_test_zero {d : ℕ}
    {R : (ℂ × (Option (Fin d) → ℂ)) → ℝ} (hR : ContDiff ℝ 1 R)
    {T : Set ℂ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ}
    (hs : energyComplexTime '' tsupport η ⊆ T)
    (hreg : ∀ τ ∈ T, ∀ q, R (τ, q) = 0 → fderiv ℝ R (τ, q) ≠ 0)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : R (fullPhysicalProjection d x) = 0) :
    fderiv ℝ (fun y => R (fullPhysicalProjection d y)) x ≠ 0 ∨
      (fun y => η (timeProjection (d + 1) 3 y)) =ᶠ[𝓝 x] (fun _ => 0) := by
  by_cases ht : (fullPhysicalProjection d x).1 ∈ T
  · exact Or.inl (fullPhysical_extension_regular hR
      (hreg _ ht (fullPhysicalProjection d x).2 hx))
  · exact Or.inr (time_test_eventually_zero_of_notMem hs ht)

end OAI.Analysis.PDE.Green
