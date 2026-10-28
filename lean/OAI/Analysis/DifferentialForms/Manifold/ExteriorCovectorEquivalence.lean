import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! # Exterior Covector Equivalence -/

namespace OAI.Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence

noncomputable section

/-!
# Continuous alternating covectors and the literal exterior-power dual

Finite-dimensionality makes every real multilinear map continuous. The usual
continuous alternating covectors therefore identify with all real-linear maps
from the real exterior power to the complex numbers. The identification is
complex-linear in the values and commutes with actual tangent pullback.
-/

open scoped BigOperators _root_.Manifold ContDiff

section FiniteDimensionalContinuity

variable {E F : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι]

/-- Finite basis expansion proves continuity of every real multilinear map.
No continuity premise is imposed on the map. -/
theorem continuous_multilinearMap_of_finiteDimensional
    (f : MultilinearMap ℝ (fun _ : ι => E) F) : Continuous f := by
  classical
  let b := Module.finBasis ℝ E
  have hexpansion (v : ι → E) :
      f v = ∑ a : ι → Fin (Module.finrank ℝ E),
        (∏ i, b.repr (v i) (a i)) • f (fun i => b (a i)) := by
    calc
      f v = f (fun i => ∑ j, b.repr (v i) j • b j) :=
        congrArg f (funext fun i => (b.sum_repr (v i)).symm)
      _ = _ := by
        rw [f.map_sum]
        simp only [f.map_smul_univ]
  have hcontinuous : Continuous (fun v : ι → E =>
      ∑ a : ι → Fin (Module.finrank ℝ E),
        (∏ i, b.repr (v i) (a i)) • f (fun i => b (a i))) := by
    apply continuous_finsetSum
    intro a _
    apply Continuous.smul ?_ continuous_const
    apply continuous_finsetProd
    intro i _
    exact (b.coord (a i)).continuous_of_finiteDimensional.comp (continuous_apply i)
  simpa only [← hexpansion] using hcontinuous

/-- In finite dimensions every algebraic alternating covector is continuous. -/
theorem continuous_alternatingMap_of_finiteDimensional (f : E [⋀^ι]→ₗ[ℝ] F) :
    Continuous f :=
  continuous_multilinearMap_of_finiteDimensional f.toMultilinearMap

end FiniteDimensionalContinuity

section ExteriorDual

variable (E : Type*) [AddCommGroup E] [Module ℝ E]

/-- The exterior-power universal property is complex-linear in complex values,
although the underlying tangent space and exterior power are real. -/
def alternatingExteriorCovectorEquiv (n : ℕ) :
    (E [⋀^Fin n]→ₗ[ℝ] ℂ) ≃ₗ[ℂ] ((⋀[ℝ]^n E) →ₗ[ℝ] ℂ) where
  toEquiv := (exteriorPower.alternatingMapLinearEquiv (R := ℝ) (M := E)
    (N := ℂ) (n := n)).toEquiv
  map_add' := (exteriorPower.alternatingMapLinearEquiv (R := ℝ) (M := E)
    (N := ℂ) (n := n)).map_add
  map_smul' c f := by
    apply exteriorPower.linearMap_ext
    ext v
    change exteriorPower.alternatingMapLinearEquiv (c • f) (exteriorPower.ιMulti ℝ n v) =
      c • exteriorPower.alternatingMapLinearEquiv f (exteriorPower.ιMulti ℝ n v)
    simp only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.smul_apply]

@[simp]
theorem alternatingExteriorCovectorEquiv_apply_ιMulti (n : ℕ)
    (f : E [⋀^Fin n]→ₗ[ℝ] ℂ) (v : Fin n → E) :
    alternatingExteriorCovectorEquiv E n f (exteriorPower.ιMulti ℝ n v) = f v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f v

@[simp]
theorem alternatingExteriorCovectorEquiv_symm_apply (n : ℕ)
    (f : (⋀[ℝ]^n E) →ₗ[ℝ] ℂ) (v : Fin n → E) :
    (alternatingExteriorCovectorEquiv E n).symm f v =
      f (exteriorPower.ιMulti ℝ n v) :=
  exteriorPower.alternatingMapLinearEquiv_symm_apply f v

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [T2Space E] [FiniteDimensional ℝ E]

/-- Forgetting continuity is a bijection for finite-dimensional real covectors. -/
def continuousAlternatingCovectorEquiv (n : ℕ) :
    (E [⋀^Fin n]→L[ℝ] ℂ) ≃ₗ[ℂ] (E [⋀^Fin n]→ₗ[ℝ] ℂ) where
  toFun := ContinuousAlternatingMap.toAlternatingMap
  invFun f := { f with cont := continuous_alternatingMap_of_finiteDimensional f }
  left_inv f := by ext v; rfl
  right_inv f := by ext v; rfl
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl

@[simp]
theorem continuousAlternatingCovectorEquiv_apply (n : ℕ)
    (f : E [⋀^Fin n]→L[ℝ] ℂ) :
    continuousAlternatingCovectorEquiv E n f = f.toAlternatingMap := rfl

@[simp]
theorem continuousAlternatingCovectorEquiv_symm_apply (n : ℕ)
    (f : E [⋀^Fin n]→ₗ[ℝ] ℂ) (v : Fin n → E) :
    (continuousAlternatingCovectorEquiv E n).symm f v = f v := rfl

/-- The literal complex-valued real exterior dual used in the official statement. -/
def exteriorCovectorEquiv (n : ℕ) :
    (E [⋀^Fin n]→L[ℝ] ℂ) ≃ₗ[ℂ] ((⋀[ℝ]^n E) →ₗ[ℝ] ℂ) :=
  (continuousAlternatingCovectorEquiv E n).trans (alternatingExteriorCovectorEquiv E n)

@[simp]
theorem exteriorCovectorEquiv_apply_ιMulti (n : ℕ)
    (f : E [⋀^Fin n]→L[ℝ] ℂ) (v : Fin n → E) :
    exteriorCovectorEquiv E n f (exteriorPower.ιMulti ℝ n v) = f v :=
  alternatingExteriorCovectorEquiv_apply_ιMulti E n f.toAlternatingMap v

@[simp]
theorem exteriorCovectorEquiv_symm_apply (n : ℕ)
    (f : (⋀[ℝ]^n E) →ₗ[ℝ] ℂ) (v : Fin n → E) :
    (exteriorCovectorEquiv E n).symm f v = f (exteriorPower.ιMulti ℝ n v) :=
  alternatingExteriorCovectorEquiv_symm_apply E n f v

end ExteriorDual

section Pullback

variable {E F : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [Module ℝ F] [ContinuousSMul ℝ F] [T2Space F] [FiniteDimensional ℝ F]

/-- Covector pullback is precomposition by the actual induced exterior-power map. -/
theorem exteriorCovectorEquiv_pullback (n : ℕ) (f : E →L[ℝ] F)
    (form : F [⋀^Fin n]→L[ℝ] ℂ) :
    exteriorCovectorEquiv E n (form.compContinuousLinearMap f) =
      (exteriorCovectorEquiv F n form).comp (exteriorPower.map n f.toLinearMap) := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, exteriorCovectorEquiv_apply_ιMulti,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, ContinuousLinearMap.coe_coe]

end Pullback

section ComplexScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Inverse complex-scalar pullback becomes the contragredient action on the
literal real exterior-power dual. -/
theorem exteriorCovectorEquiv_inverseScalar (n : ℕ) (z : ℂˣ)
    (form : E [⋀^Fin n]→L[ℝ] ℂ) :
    exteriorCovectorEquiv E n (Bidegree.scalarCovectorPullback E n (↑(z⁻¹) : ℂ) form) =
      (exteriorCovectorEquiv E n form).comp
        (exteriorPower.map n
          (ContinuousLinearMap.lsmul ℝ ℂ (↑(z⁻¹) : ℂ) : E →L[ℝ] E).toLinearMap) :=
  exteriorCovectorEquiv_pullback n
    (ContinuousLinearMap.lsmul ℝ ℂ (↑(z⁻¹) : ℂ) : E →L[ℝ] E) form

end ComplexScalar

section RealTangent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual real tangent fiber has the finite dimension of its chart model. -/
theorem finiteDimensional_realTangentSpace (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  FiniteDimensional.of_injective (TangentCoordinates.preferredTangentEquiv (E := E) x).toLinearEquiv.toLinearMap
    (TangentCoordinates.preferredTangentEquiv (E := E) x).injective

omit [FiniteDimensional ℝ E] in
/-- The actual topology on each real tangent fiber is Hausdorff. -/
theorem t2Space_realTangentSpace (x : M) : T2Space (TangentSpace 𝓘(ℝ, E) x) :=
  (TangentCoordinates.preferredTangentEquiv (E := E) x).toHomeomorph.symm.t2Space

/-- The exterior-dual identification on an actual real tangent fiber. -/
def tangentExteriorCovectorEquiv (x : M) (n : ℕ) :
    (TangentSpace 𝓘(ℝ, E) x [⋀^Fin n]→L[ℝ] ℂ) ≃ₗ[ℂ]
      ((⋀[ℝ]^n (TangentSpace 𝓘(ℝ, E) x)) →ₗ[ℝ] ℂ) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) := finiteDimensional_realTangentSpace x
  let : T2Space (TangentSpace 𝓘(ℝ, E) x) := t2Space_realTangentSpace x
  exact exteriorCovectorEquiv (TangentSpace 𝓘(ℝ, E) x) n

@[simp]
theorem tangentExteriorCovectorEquiv_apply_ιMulti (x : M) (n : ℕ)
    (form : TangentSpace 𝓘(ℝ, E) x [⋀^Fin n]→L[ℝ] ℂ)
    (v : Fin n → TangentSpace 𝓘(ℝ, E) x) :
    tangentExteriorCovectorEquiv x n form (exteriorPower.ιMulti ℝ n v) = form v := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) := finiteDimensional_realTangentSpace x
  let : T2Space (TangentSpace 𝓘(ℝ, E) x) := t2Space_realTangentSpace x
  exact exteriorCovectorEquiv_apply_ιMulti (TangentSpace 𝓘(ℝ, E) x) n form v

variable (E M) in
/-- Actual covector fields are exactly sections of the literal exterior dual. -/
def rawManifoldExteriorCovectorEquiv (n : ℕ) :
    Algebra.RawManifoldForm E M n ≃ₗ[ℂ]
      (∀ x : M, (⋀[ℝ]^n (TangentSpace 𝓘(ℝ, E) x)) →ₗ[ℝ] ℂ) :=
  LinearEquiv.piCongrRight fun x => tangentExteriorCovectorEquiv x n

@[simp]
theorem rawManifoldExteriorCovectorEquiv_apply (n : ℕ) (form : Algebra.RawManifoldForm E M n)
    (x : M) :
    rawManifoldExteriorCovectorEquiv E M n form x = tangentExteriorCovectorEquiv x n (form x) :=
  rfl

end RealTangent

attribute [local instance] ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The previously constructed actual tangent action is exactly the
contragredient exterior-power action on each real tangent fiber. -/
theorem tangentExteriorCovectorEquiv_complexAction (n : ℕ) (z : ℂˣ)
    (form : Algebra.RawManifoldForm E M n) (x : M) :
    tangentExteriorCovectorEquiv x n (Algebra.RawManifoldForm.complexAction z form x) =
      (tangentExteriorCovectorEquiv x n (form x)).comp
        (exteriorPower.map n (ComplexAction.complexTangentScalarMap x (↑(z⁻¹) : ℂ)).toLinearMap) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) := finiteDimensional_realTangentSpace x
  let : T2Space (TangentSpace 𝓘(ℝ, E) x) := t2Space_realTangentSpace x
  exact exteriorCovectorEquiv_pullback n (ComplexAction.complexTangentScalarMap x (↑(z⁻¹) : ℂ)) (form x)

/-- Pure type expressed literally in the real-linear dual of the real tangent
exterior power, with the negative integer powers from the official statement. -/
theorem hasManifoldBidegree_iff_exteriorDual_action {p q : ℕ}
    (form : Algebra.RawManifoldForm E M (p + q)) :
    ManifoldBidegree.HasManifoldBidegree E M p q form ↔
      ∀ (x : M) (z : ℂˣ),
        (tangentExteriorCovectorEquiv x (p + q) (form x)).comp
            (exteriorPower.map (p + q) (ComplexAction.complexTangentScalarMap x (↑(z⁻¹) : ℂ)).toLinearMap) =
          ((z : ℂ) ^ (-(p : ℤ)) * (star (z : ℂ)) ^ (-(q : ℤ))) •
            tangentExteriorCovectorEquiv x (p + q) (form x) := by
  rw [CovectorAction.hasManifoldBidegree_iff_tangentBidegree, CovectorAction.hasTangentBidegree_iff_section_action]
  constructor
  · intro h x z
    rw [← tangentExteriorCovectorEquiv_complexAction]
    have hx : Algebra.RawManifoldForm.complexAction z form x =
        (((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ q)⁻¹) • form x := congrFun (h z) x
    rw [hx, map_smul, CovectorAction.tangentBidegree_negative_powers]
  · intro h z
    funext x
    apply (tangentExteriorCovectorEquiv x (p + q)).injective
    change tangentExteriorCovectorEquiv x (p + q) (Algebra.RawManifoldForm.complexAction z form x) =
      tangentExteriorCovectorEquiv x (p + q)
        ((((z : ℂ) ^ p)⁻¹ * ((star (z : ℂ)) ^ q)⁻¹) • form x)
    rw [tangentExteriorCovectorEquiv_complexAction, map_smul, CovectorAction.tangentBidegree_negative_powers]
    exact h x z

end

end OAI.Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence
