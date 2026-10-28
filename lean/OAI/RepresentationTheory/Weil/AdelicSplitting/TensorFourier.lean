import OAI.RepresentationTheory.Weil.AdelicSplitting.OneCoordinate
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner

/-! # Tensor Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.TensorFourier.LocalAnalysis

noncomputable section

/-! Fourier transforms of tensor products, and compact locally constant
tensor test functions. These compute the normalization in every rank. -/

open _root_.MeasureTheory
open scoped Classical

def scalarFourier {k : Type} [Field k] [MeasurableSpace k]
    (ψ : AddChar k ℂ) (μ : Measure k) (f : k → ℂ) (x : k) : ℂ :=
  ∫ t, f t * ψ (-(x * t)) ∂μ

def tensorFunction {k : Type} (n : ℕ) (f : k → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k n) : ℂ :=
  ∏ i, f (x i)

theorem tensorFunction_locallyConstant {k : Type} [TopologicalSpace k]
    (n : ℕ) {f : k → ℂ} (hf : IsLocallyConstant f) :
    IsLocallyConstant (tensorFunction n f) := by
  have h (s : Finset (Fin n)) : IsLocallyConstant (fun x : Local.FunctionsMetaplectic.Construction.Position k n => ∏ i ∈ s, f (x i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using! (IsLocallyConstant.const (X := Local.FunctionsMetaplectic.Construction.Position k n) (1 : ℂ))
    | @insert i s hi ih =>
        simp only [Finset.prod_insert hi]
        exact (hf.comp_continuous (continuous_apply i)).mul ih
  exact h Finset.univ

theorem tensorFunction_compactSupport {k : Type} [TopologicalSpace k] [T2Space k]
    (n : ℕ) {f : k → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (tensorFunction n f) := by
  apply HasCompactSupport.intro (isCompact_pi_infinite fun _ : Fin n => hf)
  intro x hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  have hz : f (x i) = 0 := by
    by_contra hn
    exact hi (subset_tsupport f hn)
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem tensorFunction_mem {k : Type} [NormedField k]
    (n : ℕ) {f : k → ℂ} (hc : IsLocallyConstant f) (hs : HasCompactSupport f) :
    tensorFunction n f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n :=
  Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (tensorFunction_locallyConstant n hc) (tensorFunction_compactSupport n hs)

theorem fourierIntegral_tensorFunction
    {k : Type} [Field k] [MeasurableSpace k] (n : ℕ)
    (ψ : AddChar k ℂ) (μ : Measure k) [SigmaFinite μ] (f : k → ℂ) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (tensorFunction n f) =
      tensorFunction n (scalarFourier ψ μ f) := by
  funext x
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral tensorFunction scalarFourier
  simp only [Local.FunctionsMetaplectic.Construction.dot, ← Finset.sum_neg_distrib, NonarchimedeanIntertwiner.LocalAnalysis.character_finset_sum,
    ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i t => f t * ψ (-(x i * t)))

theorem scalarFourier_square_of_one_coordinate
    {k : Type} [NormedField k] [MeasurableSpace k]
    (ψ : AddChar k ℂ) (μ : Measure k) (c : ℝ)
    (hSquare : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k 1) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => μ))
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => μ)) f.val) x =
          (c : ℂ) * f.val (-x))
    {f : k → ℂ} (hc : IsLocallyConstant f) (hs : HasCompactSupport f) (x : k) :
    scalarFourier ψ μ (scalarFourier ψ μ f) x = (c : ℂ) * f (-x) := by
  let φ : Local.FunctionsMetaplectic.Construction.schwartzBruhat k 1 := ⟨tensorFunction 1 f, tensorFunction_mem 1 hc hs⟩
  have h := hSquare φ (fun _ => x)
  have hφ : φ.val = fun y => f (y 0) := by
    funext y
    simp [φ, tensorFunction]
  rw [hφ] at h
  have he : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => μ)) (fun y => f (y 0)) =
      fun y => scalarFourier ψ μ f (y 0) := funext (OneCoordinate.LocalAnalysis.fourierIntegral_one_coordinate ψ μ f)
  rw [he, OneCoordinate.LocalAnalysis.fourierIntegral_one_coordinate] at h
  exact h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.TensorFourier.LocalAnalysis
