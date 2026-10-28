import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exponential M -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential

noncomputable section

/-!
# DegreeTwo: global one-parameter subgroups

The exponential construction starts with actual invariant vector fields.
Translation of a local integral curve supplies the same existence time at
every group element, so the uniform-time theorem gives global curves.
No existence of an exponential map is an input to these results.
-/

open _root_.Manifold
open scoped _root_.Manifold _root_.Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ∞ G]

local instance : LieGroup (𝓘(ℝ, E)) (minSmoothness ℝ 3) G := by
  rw [minSmoothness_of_isRCLikeNormedField]
  infer_instance

omit [LieGroup (𝓘(ℝ, E)) ∞ G] in
@[simp]
theorem invariant_one (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    mulInvariantVectorField v (1 : G) = v := by
  unfold mulInvariantVectorField
  have hid : (fun x : G => 1 * x) = id := funext one_mul
  rw [hid, mfderiv_id]
  rfl

/-- Left translation pushes an invariant vector field to itself. -/
theorem invariant_pushforward (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (g h : G) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) h
        (mulInvariantVectorField v h) = mulInvariantVectorField v (g * h) := by
  have hg : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiable (by simp)
  have hh : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => h * x) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiable (by simp)
  have hc := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) (1 : G) (hg (h * 1)) (hh 1)
  have heq : (fun x : G => g * x) ∘ (fun x : G => h * x) =
      (fun x => (g * h) * x) := by
    funext x
    exact (mul_assoc g h x).symm
  rw [heq, mul_one] at hc
  exact (congrArg (fun f => f v) hc).symm

/-- Translating an integral curve preserves its invariant vector field. -/
theorem integralCurveOn_mul (v : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (g : G) {γ : ℝ → G} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s) :
    IsMIntegralCurveOn (fun t => g * γ t) (mulInvariantVectorField v) s := by
  have hg : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiable (by simp)
  intro t ht
  have hc := (hg (γ t)).hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)
  have he : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g * x) (γ t)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t)) := by
    apply ContinuousLinearMap.ext
    intro r
    simp [invariant_pushforward]
  exact hc.congr_mfderiv he

theorem integralCurve_mul (v : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (g : G) {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) :
    IsMIntegralCurve (fun t => g * γ t) (mulInvariantVectorField v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn]
  exact integralCurveOn_mul v g (hγ.isMIntegralCurveOn Set.univ)

/-- Actual invariant vector fields have global integral curves through every
point of a Lie group modeled on a complete real normed space. -/
theorem exists_global_integralCurve [CompleteSpace E] [T2Space G]
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (g : G) :
    ∃ γ : ℝ → G, γ 0 = g ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  have hv : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent 1
      (fun x : G => (mulInvariantVectorField v x : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by simp)
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (t₀ := (0 : ℝ)) (x₀ := (1 : G)) hv.contMDiffAt
  obtain ⟨ε, hε, hγε⟩ := isMIntegralCurveAt_iff'.mp hγ
  have hinterval : IsMIntegralCurveOn γ (mulInvariantVectorField v) (Set.Ioo (-ε) ε) := by
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hγε
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hv hε _ g
  intro x
  exact ⟨fun t => x * γ t, by simp [hγ0], integralCurveOn_mul v x hinterval⟩

/-- Uniqueness of the global integral curve proves the one-parameter
subgroup law, with its prescribed initial velocity. -/
theorem exists_oneParameterSubgroup [CompleteSpace E] [T2Space G]
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ γ : ℝ → G, γ 0 = 1 ∧
      IsMIntegralCurve γ (mulInvariantVectorField v) ∧
      ∀ s t : ℝ, γ (s + t) = γ s * γ t := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_integralCurve v (1 : G)
  refine ⟨γ, hγ0, hγ, ?_⟩
  intro s t
  have hv : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent 1
      (fun x : G => (mulInvariantVectorField v x : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by simp)
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv
    (hγ.comp_add s) (integralCurve_mul v (γ s) hγ)
    (t₀ := (0 : ℝ)) (by simp [hγ0])
  simpa only [Function.comp_apply, add_comm t s] using congrFun he t

section ChosenCurve

variable [CompleteSpace E] [T2Space G]

/-- The global integral curve with prescribed velocity and identity basepoint.
The choice is unique by the ODE uniqueness theorem. -/
def curve (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : ℝ → G :=
  (exists_oneParameterSubgroup v).choose

@[simp]
theorem curve_zero (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : curve v 0 = 1 :=
  (exists_oneParameterSubgroup v).choose_spec.1

theorem curve_integral (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    IsMIntegralCurve (curve v) (mulInvariantVectorField v) :=
  (exists_oneParameterSubgroup v).choose_spec.2.1

theorem curve_add (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s t : ℝ) :
    curve v (s + t) = curve v s * curve v t :=
  (exists_oneParameterSubgroup v).choose_spec.2.2 s t

theorem curve_continuous (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : Continuous (curve v) :=
  (curve_integral v).continuous

/-- An invariant integral curve is continuously differentiable. The derivative
is read in a fixed tangent trivialization, where the smooth vector field is
continuous. -/
theorem curve_contMDiff_one (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 (curve v) := by
  intro t₀
  let S : ℝ → TangentBundle (𝓘(ℝ, E)) G :=
    fun t => ⟨curve v t, mulInvariantVectorField v (curve v t)⟩
  let T := trivializationAt E (TangentSpace (𝓘(ℝ, E))) (curve v t₀)
  let U : Set ℝ := S ⁻¹' T.source
  let φ : ℝ → E := fun t => (T (S t)).2
  have hS : Continuous S :=
    (contMDiff_mulInvariantVectorField v).continuous.comp (curve_continuous v)
  have hU : IsOpen U := T.open_source.preimage hS
  have ht₀ : t₀ ∈ U := by
    change S t₀ ∈ T.source
    simp [T, S, TangentBundle.trivializationAt_source]
  have hφ : ContinuousOn φ U :=
    (T.continuousOn.comp hS.continuousOn (fun _ ht => ht)).snd
  have hder (t : ℝ) (ht : t ∈ U) :
      HasDerivAt (extChartAt (𝓘(ℝ, E)) (curve v t₀) ∘ curve v) (φ t) t := by
    have hsrc : curve v t ∈ (extChartAt (𝓘(ℝ, E)) (curve v t₀)).source := by
      simpa only [U, S, T, Set.mem_preimage, TangentBundle.trivializationAt_source,
        extChartAt_source] using ht
    have h := ((curve_integral v).isMIntegralCurveOn Set.univ).hasDerivWithinAt
      (t₀ := t₀) (Set.mem_univ t) hsrc
    exact h.hasDerivAt Filter.univ_mem
  have hchart : ContDiffAt ℝ 1
      (extChartAt (𝓘(ℝ, E)) (curve v t₀) ∘ curve v) t₀ := by
    apply contDiffAt_one_iff.mpr
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (φ t), U, hU.mem_nhds ht₀, ?_, ?_⟩
    · exact (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous.comp_continuousOn hφ
    · intro t ht
      exact (hder t ht).hasFDerivAt
  exact contMDiffAt_iff_target.mpr ⟨(curve_continuous v).continuousAt, hchart.contMDiffAt⟩

/-- Rescaling initial velocity is exactly rescaling time. -/
theorem curve_smul (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (a t : ℝ) :
    curve (a • v) t = curve v (t * a) := by
  have hv : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent 1
      (fun x : G => (mulInvariantVectorField (a • v) x : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField (a • v)).of_le (by simp)
  have hscaled : IsMIntegralCurve (curve v ∘ (· * a))
      (mulInvariantVectorField (a • v)) := by
    rw [mulInvariantVectorField_smul]
    exact (curve_integral v).comp_mul a
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv
    (curve_integral (a • v)) hscaled (t₀ := (0 : ℝ)) (by simp)
  exact congrFun he t

/-- The exponential is defined from the constructed global integral curve. -/
def exp (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : G := curve v 1

theorem exp_smul (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (t : ℝ) :
    exp (t • v) = curve v t := by
  simpa only [exp, one_mul] using curve_smul v t 1

@[simp]
theorem exp_zero : exp (0 : GroupLieAlgebra (𝓘(ℝ, E)) G) = 1 := by
  simpa only [zero_smul, curve_zero] using exp_smul (0 : GroupLieAlgebra (𝓘(ℝ, E)) G) 0

omit [CompleteSpace E] [T2Space G] in
/-- In a commutative Lie group the product of invariant integral curves has
initial velocity equal to the sum of their initial velocities. -/
theorem product_integralCurve
    (hcomm : ∀ a b : G, a * b = b * a)
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G)
    {γ δ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (hδ : IsMIntegralCurve δ (mulInvariantVectorField w)) :
    IsMIntegralCurve (fun t => γ t * δ t) (mulInvariantVectorField (v + w)) := by
  have hm : MDifferentiable ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
      (fun p : G × G => p.1 * p.2) :=
    (contMDiff_mul (𝓘(ℝ, E)) (n := ∞)).mdifferentiable (by simp)
  intro t
  have hc := (hm (γ t, δ t)).hasMFDerivAt.comp t ((hγ t).prodMk (hδ t))
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
      (fun p : G × G => p.1 * p.2) (γ t, δ t)
      (r • mulInvariantVectorField v (γ t), r • mulInvariantVectorField w (δ t)) =
    r • mulInvariantVectorField (v + w) (γ t * δ t)
  erw [mfderiv_prod_eq_add_apply (hm (γ t, δ t))]
  have heq : (fun x : G => x * δ t) = (fun x => δ t * x) := funext fun x => hcomm x (δ t)
  dsimp only
  erw [heq, map_smul, map_smul, invariant_pushforward, invariant_pushforward,
    hcomm (δ t) (γ t)]
  simp only [mulInvariantVectorField_add, Pi.add_apply, smul_add]

/-- Addition of velocities multiplies the corresponding one-parameter
subgroups in a commutative Lie group. -/
theorem curve_add_velocity (hcomm : ∀ a b : G, a * b = b * a)
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) (t : ℝ) :
    curve (v + w) t = curve v t * curve w t := by
  have hv : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent 1
      (fun x : G => (mulInvariantVectorField (v + w) x : TangentBundle (𝓘(ℝ, E)) G)) :=
    (contMDiff_mulInvariantVectorField (v + w)).of_le (by simp)
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv
    (curve_integral (v + w))
    (product_integralCurve hcomm v w (curve_integral v) (curve_integral w))
    (t₀ := (0 : ℝ)) (by simp)
  exact congrFun he t

theorem exp_add (hcomm : ∀ a b : G, a * b = b * a)
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) : exp (v + w) = exp v * exp w :=
  curve_add_velocity hcomm v w 1

end ChosenCurve

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E C] [CommGroup C]
  [LieGroup (𝓘(ℝ, E)) ∞ C] [CompleteSpace E] [T2Space C]

/-- The constructed exponential in the tangent model's ordinary vector coordinates. -/
def expMap (v : E) : C := exp (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from v)

theorem expMap_add (v w : E) :
    expMap (C := C) (v + w) = expMap (C := C) v * expMap (C := C) w :=
  exp_add (fun a b : C => mul_comm a b) _ _

theorem expMap_sum {ι : Type*} (s : Finset ι) (v : ι → E) :
    expMap (C := C) (∑ i ∈ s, v i) = ∏ i ∈ s, expMap (C := C) (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact exp_zero (E := E) (G := C)
  | @insert i s hi hs =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, expMap_add, hs]

/-- Finite coordinates express the exponential as a product of the already
constructed one-parameter subgroups; no parameter-dependence theorem for ODEs
is assumed. -/
theorem expMap_basis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (x : E) :
    expMap (C := C) x =
      ∏ i, curve (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from b i) (b.repr x i) := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  rw [expMap_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact exp_smul (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from b i) (b.repr x i)

omit [CompleteSpace E] [T2Space C] in
/-- Products of differentiable maps into a Lie group are differentiable. -/
theorem mdifferentiable_finset_prod {ι : Type*} (s : Finset ι) (f : ι → E → C)
    (hf : ∀ i ∈ s, MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f i)) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using mdifferentiable_const
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hi' := hf i (Finset.mem_insert_self i s)
    have hm := (contMDiff_mul (𝓘(ℝ, E)) (n := ∞) (G := C)).mdifferentiable (by simp)
    intro x
    simpa only [Finset.prod_insert hi, Function.comp_def] using
      (hm (f i x, ∏ j ∈ s, f j x)).comp x ((hi' x).prodMk (hs x))

/-- The exponential on a finite-dimensional commutative Lie group is
differentiable, proved from finite coordinates and the integral curves. -/
theorem expMap_mdifferentiable [FiniteDimensional ℝ E] :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (expMap (E := E) (C := C)) := by
  let b := Module.finBasis ℝ E
  have he : expMap (E := E) (C := C) = fun x =>
      ∏ i, curve (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from b i) (b.repr x i) :=
    funext (expMap_basis b)
  rw [he]
  apply mdifferentiable_finset_prod
  intro i _ x
  exact ((curve_integral (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from b i))
      (b.repr x i)).mdifferentiableAt.comp x
    ((b.coord i).toContinuousLinearMap.differentiableAt.mdifferentiableAt)

theorem expMap_continuous [FiniteDimensional ℝ E] :
    Continuous (expMap (E := E) (C := C)) :=
  (expMap_mdifferentiable (E := E) (C := C)).continuous

/-- Continuous differentiability follows from the finite-coordinate product
formula and the continuously differentiable invariant integral curves. -/
theorem expMap_contMDiff_one [FiniteDimensional ℝ E] :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (expMap (E := E) (C := C)) := by
  let b := Module.finBasis ℝ E
  have he : expMap (E := E) (C := C) = fun x =>
      ∏ i, curve (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from b i) (b.repr x i) :=
    funext (expMap_basis b)
  rw [he]
  apply ContMDiff.prod
  intro i _
  exact (curve_contMDiff_one (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from b i)).comp
    (b.coord i).toContinuousLinearMap.contDiff.contMDiff

/-- The fixed tangent model identifies its vectors with the tangent space at
an individual point. This is the chart-model identification used by mfderiv. -/
def modelToTangent (x : C) : E ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x := by
  change E ≃L[ℝ] E
  exact ContinuousLinearEquiv.refl ℝ E

/-- The differential of the exponential at zero is the identity on the
tangent model. It is computed on each line using the actual integral curve. -/
theorem hasMFDerivAt_expMap_zero [FiniteDimensional ℝ E] :
    HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (expMap (E := E) (C := C)) (0 : E)
      (modelToTangent (E := E) (expMap (C := C) (0 : E))).toContinuousLinearMap := by
  have hd := (expMap_mdifferentiable (E := E) (C := C) (0 : E)).hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro v
  change E at v
  let l : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight v
  have he : expMap (E := E) (C := C) ∘ l =
      curve (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from v) := by
    funext t
    exact exp_smul (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from v) t
  have hc := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    (0 : ℝ) (expMap_mdifferentiable (E := E) (C := C) (l 0))
    l.mdifferentiableAt
  rw [he, (curve_integral (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from v) 0).mfderiv] at hc
  have hl : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) l (0 : ℝ) = l := l.hasMFDerivAt.mfderiv
  erw [hl] at hc
  have hv := congrArg (fun f => f (1 : ℝ)) hc
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (expMap (E := E) (C := C)) (0 : E)) v = v
  have hv' := hv.symm
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (expMap (E := E) (C := C)) (l 0)) (l 1) =
    (1 : ℝ →L[ℝ] ℝ) 1 • mulInvariantVectorField
      (show GroupLieAlgebra (𝓘(ℝ, E)) C from v)
      (curve (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from v) 0) at hv'
  have hl0 : l 0 = 0 := map_zero l
  have hl1 : l 1 = v := by simp [l]
  erw [hl0, hl1, one_apply_eq_self, one_smul, curve_zero, invariant_one] at hv'
  exact hv'

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential
