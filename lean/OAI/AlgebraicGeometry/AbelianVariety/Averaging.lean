import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Averaging -/

namespace OAI.AlgebraicGeometry.AbelianVariety.Averaging.Constructions.ExteriorCohomology

noncomputable section

/-!
# Haar averaging for ExteriorCohomology

The left-translation coefficients of actual smooth manifold forms are smooth.
Integrating these coefficients gives a linear projection onto invariant forms,
with the expected translation law for Haar measure.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter _root_.MeasureTheory

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] {n : ℕ}

def leftCoefficient (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (g : G) :
    E [⋀^Fin n]→L[ℝ] ℂ :=
  ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback (fun x : G => g * x)) 1

theorem leftCoefficient_inChart (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (c d : OpenPartialHomeomorph G E) (hc : c ∈ atlas E G) (hd : d ∈ atlas E G)
    (h1 : (1 : G) ∈ d.source) {y : E} (hy : y ∈ c.target) :
    leftCoefficient form (c.symm y) =
      ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).inChart c y).compContinuousLinearMap
        ((fderiv ℝ (fun w => c (c.symm y * d.symm w)) (d 1)).comp
          (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap d 1)) := by
  have hp := (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback_inChart
    (fun x : G => c.symm y * x) d c hd hc (d.map_source h1)
    (by simpa only [d.left_inv h1, mul_one] using c.map_target hy)
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  rw [d.left_inv h1, mul_one, c.right_inv hy] at hp
  have hv := congrArg (fun α : E [⋀^Fin n]→L[ℝ] ℂ =>
    α.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap d (1 : G))) hp
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ d hd h1] at hv
  exact hv

theorem leftCoefficient_contDiffAt_inChart (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (c : OpenPartialHomeomorph G E) (hc : c ∈ atlas E G) {y : E} (hy : y ∈ c.target) :
    ContDiffAt ℝ ∞ (fun z => leftCoefficient form (c.symm z)) y := by
  let d := chartAt E (1 : G)
  have hd : d ∈ atlas E G := chart_mem_atlas E (1 : G)
  have h1 : (1 : G) ∈ d.source := mem_chart_source E (1 : G)
  have hcinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
  have hdinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d.symm (d 1) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) (d.map_source h1)
  have hm : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
      (fun z : E × E => c.symm z.1 * d.symm z.2) (y, d 1) :=
    (hcinv.comp (y, d 1) contDiffAt_fst.contMDiffAt).mul
      (hdinv.comp (y, d 1) contDiffAt_snd.contMDiffAt)
  have hc' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c (c.symm y * d.symm (d 1)) := by
    rw [d.left_inv h1, mul_one]
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) (c.map_target hy)
  have ht : ContDiffAt ℝ ∞
      (fun z : E × E => c (c.symm z.1 * d.symm z.2)) (y, d 1) :=
    (hc'.comp (y, d 1) hm).contDiffAt
  have hder : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (fun w => c (c.symm z * d.symm w)) (d 1)) y :=
    ht.fderiv contDiffAt_const (by simp)
  have hform := Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart (form := (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n))
    form.smooth c hc hy
  let L : E →L[ℝ] E := Analysis.DifferentialForms.Manifold.Charts.chartTangentMap d (1 : G)
  have hL : ContDiffAt ℝ ∞ (fun _ : E => L) y := contDiffAt_const
  have hs := Analysis.DifferentialForms.Manifold.Alternatization.contDiffAt_alternating_compContinuousLinearMap hform (hder.clm_comp hL)
  apply hs.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds hy] with z hz
  exact leftCoefficient_inChart form c d hc hd h1 hz

theorem leftCoefficient_contMDiff (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E [⋀^Fin n]→L[ℝ] ℂ) ∞ (leftCoefficient form) := by
  intro x
  let c := chartAt E x
  have hc : c ∈ atlas E G := chart_mem_atlas E x
  have hx : x ∈ c.source := mem_chart_source E x
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hx
  have hs := (leftCoefficient_contDiffAt_inChart form c hc (c.map_source hx)).contMDiffAt
  apply (hs.comp x hchart).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hx] with z hz
  exact congrArg (leftCoefficient form) (c.left_inv hz).symm

def leftCoefficientLinear (g : G) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n →ₗ[ℂ] (E [⋀^Fin n]→L[ℝ] ℂ) where
  toFun form := leftCoefficient form g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem leftCoefficient_pullback (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (g h : G) :
    leftCoefficient (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x : G => g * x)
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form) h =
        leftCoefficient form (g * h) := by
  have he : (fun x : G => g * x) ∘ (fun x : G => h * x) =
      (fun x : G => (g * h) * x) := by funext x; exact (mul_assoc g h x).symm
  have hp := (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback_comp (fun x : G => h * x)
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiable (by simp))
    (fun x : G => g * x)
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiable (by simp))
  rw [he] at hp
  exact (congrFun hp 1).symm

theorem leftCoefficient_of_invariant (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (hf : form ∈ InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n) (g : G) :
    leftCoefficient form g = form 1 := by
  have hi := (InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff form).mp hf g
  exact congrArg (fun η : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n => η 1) hi

variable [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  (μ : Measure G) [IsFiniteMeasure μ]

theorem leftCoefficient_integrable (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    Integrable (leftCoefficient form) μ :=
  (leftCoefficient_contMDiff form).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def averageCoefficients : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n →ₗ[ℂ] (E [⋀^Fin n]→L[ℝ] ℂ) where
  toFun form := ∫ g, leftCoefficient form g ∂μ
  map_add' form other := integral_add (leftCoefficient_integrable μ form)
    (leftCoefficient_integrable μ other)
  map_smul' a form := integral_smul a (leftCoefficient form)

def averageForms : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n :=
  (InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n).subtype.comp
    ((InvariantClosed.Constructions.ExteriorCohomology.invariantFormsEvalEquiv n).symm.toLinearMap.comp (averageCoefficients μ))

theorem averageForms_mem (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    averageForms μ form ∈ InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n :=
  ((InvariantClosed.Constructions.ExteriorCohomology.invariantFormsEvalEquiv (E := E) (G := G) n).symm
    (averageCoefficients (E := E) (G := G) μ form)).property

theorem averageForms_of_invariant [IsProbabilityMeasure μ] (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (hf : form ∈ InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n) :
    averageForms μ form = form := by
  have he : averageCoefficients μ form = form 1 := by
    change (∫ g, leftCoefficient form g ∂μ) = form 1
    have hc : leftCoefficient form = fun _ : G => (form 1 : E [⋀^Fin n]→L[ℝ] ℂ) :=
      funext (leftCoefficient_of_invariant form hf)
    rw [hc]
    have hi := integral_const (E := E [⋀^Fin n]→L[ℝ] ℂ) (μ := μ) (form 1)
    rw [probReal_univ] at hi
    exact hi.trans (one_smul ℝ (form 1))
  change InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (E := E) (G := G)
    (averageCoefficients (E := E) (G := G) μ form) = form
  rw [he]
  exact InvariantClosed.Constructions.ExteriorCohomology.invariantForm_eq_from_value ⟨form, hf⟩

theorem averageForms_pullback [Measure.IsMulLeftInvariant μ]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (g : G) :
    averageForms μ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x : G => g * x)
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form) = averageForms μ form := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ, E)) (n := ∞)
  apply congrArg (fun α => InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (E := E) (G := G) α)
  change (∫ h, leftCoefficient _ h ∂μ) = ∫ h, leftCoefficient form h ∂μ
  simp only [leftCoefficient_pullback]
  exact integral_mul_left_eq_self (μ := μ) (leftCoefficient (E := E) form) g

theorem averageForms_closed [IsMulCommutative G] (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (averageForms μ form) = 0 :=
  InvariantClosed.Constructions.ExteriorCohomology.invariantForms_closed _ (averageForms_mem μ form)

variable [T2Space G]

def compactGroupHaar : Measure G :=
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ, E)) (n := ∞)
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)

instance compactGroupHaar_isHaarMeasure :
    (compactGroupHaar (E := E) (G := G)).IsHaarMeasure := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ, E)) (n := ∞)
  exact inferInstanceAs (Measure.IsHaarMeasure
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)))

instance compactGroupHaar_isProbabilityMeasure :
    IsProbabilityMeasure (compactGroupHaar (E := E) (G := G)) where
  measure_univ := by
    let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ, E)) (n := ∞)
    exact Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G))

end

end OAI.AlgebraicGeometry.AbelianVariety.Averaging.Constructions.ExteriorCohomology
