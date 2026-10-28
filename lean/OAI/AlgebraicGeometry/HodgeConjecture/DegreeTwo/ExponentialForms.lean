import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialSmooth
import OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed

/-! # Exponential Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialForms.Constructions.Exponential

noncomputable section

/-!
# DegreeTwo: invariant forms in exponential coordinates

The logarithmic derivative of the constructed exponential is the identity.
Consequently its pullback sends an invariant differential form to the constant
form given by its value at the identity. Both derivatives and pullbacks are the
actual manifold operations used by the de Rham integration comparison.
-/

open _root_.Manifold
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace C] [ChartedSpace E C] [CommGroup C]
  [LieGroup (𝓘(ℝ, E)) ∞ C] [T2Space C]

/-- Left translation back to the identity cancels the differential of exp. -/
theorem logarithmicDerivative_expMap (v w : E) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun y : C => (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) v)⁻¹ * y)
      (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) v)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) v w) = w := by
  let f := ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)
  let t : C → C := fun y => (f v)⁻¹ * y
  have ht : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) t (f v) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiableAt (by simp)
  have hf := ExponentialM.Constructions.Exponential.expMap_mdifferentiable (E := E) (C := C)
  have hs : HasFDerivAt (fun x : E => x - v) (ContinuousLinearMap.id ℝ E) v := by
    simpa using (hasFDerivAt_id v).sub_const v
  have he : t ∘ f = f ∘ (fun x : E => x - v) := by
    funext x
    change (f v)⁻¹ * f x = f (x - v)
    have h := ExponentialM.Constructions.Exponential.expMap_add (E := E) (C := C) v (x - v)
    have hvx : v + (x - v) = x := by abel
    rw [hvx] at h
    exact (inv_mul_eq_iff_eq_mul).mpr h
  have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) v ht (hf v)
  rw [he] at hd
  have hd' := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) (f := fun x : E => x - v) (g := f)
    v (hf (v - v)) hs.differentiableAt.mdifferentiableAt
  erw [hd', sub_self, ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero.mfderiv, hs.hasMFDerivAt.mfderiv] at hd
  exact (congrArg (fun l => l w) hd).symm

/-- Invariant forms pull back under exp to their constant identity covector. -/
theorem invariantRawForm_pullback_expMap {n : ℕ}
    (α : TangentSpace (𝓘(ℝ, E)) (1 : C) [⋀^Fin n]→L[ℝ] ℂ) (v : E) :
    (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantRawForm α).pullback (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) v = α := by
  ext w
  simp only [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback_apply, AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantRawForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  apply congrArg α
  funext i
  exact logarithmicDerivative_expMap v (w i)

/-- The same equality for actual smooth forms and their actual smooth pullback. -/
theorem invariantSmoothForm_pullback_expMap {n : ℕ}
    (α : TangentSpace (𝓘(ℝ, E)) (1 : C) [⋀^Fin n]→L[ℝ] ℂ) (v : E) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) ExponentialSmooth.Constructions.Exponential.expMap_contMDiff
      (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm α) v = α :=
  invariantRawForm_pullback_expMap α v

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialForms.Constructions.Exponential
