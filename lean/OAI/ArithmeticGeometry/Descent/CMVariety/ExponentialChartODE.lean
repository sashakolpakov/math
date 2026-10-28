import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Exponential Chart ODE -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE.Abelian

noncomputable section

/-!
The actual invariant-vector-field exponential satisfies the derivative
ODE of the actual group multiplication in any differentiable chart at
the identity. The tangent velocity is the actual derivative of the
inverse chart; no exponential/chart differential comparison is assumed.
-/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential
open scoped _root_.Manifold ContDiff

variable {E V G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ∞ G]

def chartVelocity (c : OpenPartialHomeomorph G V) (v : V) : GroupLieAlgebra (𝓘(ℝ, E)) G :=
  mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) c.symm 0 v

theorem chartMultiplication_fderiv
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (x v : V) (hx : x ∈ c.target) :
    fderiv ℝ (fun y => c (c.symm x * c.symm y)) 0 v =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, V)) c (c.symm x)
        (mulInvariantVectorField (chartVelocity c v) (c.symm x)) := by
  have hz : (0 : V) ∈ c.target := h0 ▸ c.map_source h1
  have hinv0 : c.symm 0 = (1 : G) := by
    rw [← h0, c.left_inv h1]
  let L : G → G := fun g => c.symm x * g
  have hL : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) L :=
    (contMDiff_mul_left (n := ∞)).mdifferentiable (by simp)
  have hInv := hc.mdifferentiableAt_symm hz
  have hprod : L (c.symm 0) = c.symm x := by
    change c.symm x * c.symm 0 = c.symm x
    rw [hinv0, mul_one]
  have hC : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) c (L (c.symm 0)) := by
    rw [hprod]
    exact hc.mdifferentiableAt (c.map_target hx)
  have hinner := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    (0 : V) (hL (c.symm 0)) hInv
  have houter := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, V))
    (0 : V) hC ((hL (c.symm 0)).comp 0 hInv)
  rw [hinner] at houter
  rw [mfderiv_eq_fderiv] at houter
  have h := congrArg (fun f : V →L[ℝ] V => f v) houter
  change fderiv ℝ (fun y => c (c.symm x * c.symm y)) 0 v =
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, V)) c (L (c.symm 0))
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) L (c.symm 0)
        (mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) c.symm 0 v)) at h
  erw [hprod, hinv0] at h
  exact h

theorem inverse_chartMultiplication_field
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (x v : V) (hx : x ∈ c.target) :
    mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) c.symm x
        (fderiv ℝ (fun y => c (c.symm x * c.symm y)) 0 v) =
      mulInvariantVectorField (chartVelocity c v) (c.symm x) := by
  rw [chartMultiplication_fderiv c hc h1 h0 x v hx]
  have hd := hc.symm_comp_deriv (c.map_target hx)
  rw [c.right_inv hx] at hd
  exact congrArg (fun D : E →L[ℝ] E =>
    D (mulInvariantVectorField (chartVelocity (E := E) c v) (c.symm x))) hd

/-- A solution of the multiplication ODE inside the chart transports
to an integral curve of the actual invariant vector field. -/
theorem chartODE_isMIntegralCurveOn
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (v : V) (δ : ℝ → V) (J : Set ℝ)
    (htarget : ∀ t ∈ J, δ t ∈ c.target)
    (hδ : ∀ t ∈ J,
      HasDerivAt δ (fderiv ℝ (fun y => c (c.symm (δ t) * c.symm y)) 0 v) t) :
    IsMIntegralCurveOn (c.symm ∘ δ)
      (mulInvariantVectorField (chartVelocity (E := E) c v)) J := by
  intro t ht
  have hd := (hc.mdifferentiableAt_symm (htarget t ht)).hasMFDerivAt.comp t
    (hδ t ht).hasFDerivAt.hasMFDerivAt
  apply hd.hasMFDerivWithinAt.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) c.symm (δ t)
      (r • fderiv ℝ (fun y => c (c.symm (δ t) * c.symm y)) 0 v) =
    r • mulInvariantVectorField (chartVelocity (E := E) c v) (c.symm (δ t))
  let L : V →L[ℝ] E := mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) c.symm (δ t)
  have hw : L (fderiv ℝ (fun y => c (c.symm (δ t) * c.symm y)) 0 v) =
      mulInvariantVectorField (chartVelocity (E := E) c v) (c.symm (δ t)) :=
    inverse_chartMultiplication_field c hc h1 h0 _ v (htarget t ht)
  change L (r • fderiv ℝ (fun y => c (c.symm (δ t) * c.symm y)) 0 v) = _
  rw [map_smul, hw]
  rfl

variable [CompleteSpace E] [T2Space G]

/-- The actual global invariant integral curve satisfies the local
ordinary differential equation in the chart coordinates. -/
theorem curve_in_chart_hasDerivAt
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (v : V) (t : ℝ) (ht : AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve (E := E) (chartVelocity (E := E) c v) t ∈ c.source) :
    HasDerivAt (fun τ => c (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve (E := E) (chartVelocity (E := E) c v) τ))
      (fderiv ℝ (fun y => c (c.symm (c (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve (E := E) (chartVelocity (E := E) c v) t)) * c.symm y)) 0 v) t := by
  let γ : ℝ → G := AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve (E := E) (chartVelocity (E := E) c v)
  let w : E := mulInvariantVectorField (chartVelocity (E := E) c v) (γ t)
  let D : E →L[ℝ] V := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, V)) c (γ t)
  have hd : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, V)) (c ∘ γ) t
      (D.comp ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :=
    (hc.mdifferentiableAt ht).hasMFDerivAt.comp t
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve_integral (E := E) (chartVelocity (E := E) c v) t)
  have hfd : HasFDerivAt (c ∘ γ) (D.comp ((1 : ℝ →L[ℝ] ℝ).smulRight w)) t := hd.hasFDerivAt
  have h : HasDerivAt (c ∘ γ) (D w) t := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, one_smul] using hfd.hasDerivAt
  rw [chartMultiplication_fderiv c hc h1 h0 _ v (c.map_source ht), c.left_inv ht]
  exact h

/-- Uniqueness identifies any constructed chart-ODE solution starting
at zero with the actual exponential throughout its interval of definition. -/
theorem chartODE_eq_exponential
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (v : V) (δ : ℝ → V) (εδ : ℝ) (hε : 0 < εδ) (hδ0 : δ 0 = 0)
    (htarget : ∀ t ∈ Set.Ioo (-εδ) εδ, δ t ∈ c.target)
    (hδ : ∀ t ∈ Set.Ioo (-εδ) εδ,
      HasDerivAt δ (fderiv ℝ (fun y => c (c.symm (δ t) * c.symm y)) 0 v) t) :
    ∀ t ∈ Set.Ioo (-εδ) εδ,
      c.symm (δ t) = AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E) (t • chartVelocity (E := E) c v) := by
  let : LieGroup (𝓘(ℝ, E)) (minSmoothness ℝ 3) G := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hv : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent 1
      (fun x : G => (⟨x, mulInvariantVectorField (chartVelocity (E := E) c v) x⟩ :
        TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField (chartVelocity (E := E) c v)).of_le (by simp)
  have hinit : (c.symm ∘ δ) 0 = AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve (E := E) (chartVelocity (E := E) c v) 0 := by
    simp only [Function.comp_apply, hδ0, AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve_zero]
    rw [← h0, c.left_inv h1]
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (show (0 : ℝ) ∈ Set.Ioo (-εδ) εδ by constructor <;> linarith) hv
    (chartODE_isMIntegralCurveOn c hc h1 h0 v δ _ htarget hδ)
    ((AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.curve_integral (E := E) (chartVelocity (E := E) c v)).isMIntegralCurveOn _) hinit
  intro t ht
  rw [AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp_smul]
  exact heq ht

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE.Abelian
