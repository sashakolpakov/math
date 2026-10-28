import OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialSmooth

/-! # Chart Endomorphism Derivative -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian

noncomputable section

section

/-!
The exponential expressed in a differentiable identity chart has identity
derivative at zero. Its tangent identification is the actual derivative
of the inverse chart, and its exponential is the native invariant flow.
-/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialSmooth.Constructions.Exponential
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E V G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup (𝓘(ℝ, E)) ∞ G] [T2Space G]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [LieGroup (𝓘(ℝ, E)) ∞ G] [T2Space G] in
/-- The inverse chart supplies the actual linear tangent identification. -/
def chartTangentMap (c : OpenPartialHomeomorph G V) : V →L[ℝ] E :=
  mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, E)) c.symm 0

omit [FiniteDimensional ℝ E] in
/-- The native exponential using the tangent coordinates of this chart. -/
def chartExponential (c : OpenPartialHomeomorph G V) (v : V) : G :=
  AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := E) (C := G) (chartTangentMap (E := E) c v)

omit [FiniteDimensional ℝ E] in
theorem chartExponential_zero (c : OpenPartialHomeomorph G V) :
    chartExponential (E := E) c 0 = (1 : G) := by
  change AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (G := G) (chartTangentMap (E := E) c 0) = 1
  rw [map_zero]
  exact AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp_zero (E := E) (G := G)

theorem chartExponential_mdifferentiable (c : OpenPartialHomeomorph G V) :
    MDifferentiable (𝓘(ℝ, V)) (𝓘(ℝ, E)) (chartExponential (E := E) c) :=
  (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap_mdifferentiable (E := E) (C := G)).comp (chartTangentMap (E := E) c).mdifferentiable

omit [FiniteDimensional ℝ E] in
theorem chartExponential_add (c : OpenPartialHomeomorph G V) (v w : V) :
    chartExponential (E := E) c (v + w) =
      chartExponential (E := E) c v * chartExponential (E := E) c w := by
  change AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := G) (chartTangentMap (E := E) c (v + w)) = _
  rw [map_add, AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap_add]
  rfl

theorem chartExponentialCoordinates_hasFDerivAt_zero
    (c : OpenPartialHomeomorph G V)
    (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0) :
    HasFDerivAt (fun v => c (chartExponential (E := E) c v))
      (ContinuousLinearMap.id ℝ V) 0 := by
  let L := chartTangentMap (E := E) c
  have hL0 : L 0 = 0 := map_zero L
  have hexp : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (E := E) (C := G))
      (L 0) (ContinuousLinearMap.id ℝ E) := by
    rw [hL0]
    exact AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero
  have hinner : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) (chartExponential (E := E) c) 0 L := by
    have h := hexp.comp 0 L.hasMFDerivAt
    apply h.congr_mfderiv
    ext v
    rfl
  let D : E →L[ℝ] V := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, V)) c 1
  have houter : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) c (chartExponential (E := E) c 0) D := by
    rw [chartExponential_zero]
    exact (hc.mdifferentiableAt h1).hasMFDerivAt
  have hder : HasFDerivAt (fun v => c (chartExponential (E := E) c v)) (D.comp L) 0 :=
    (houter.comp 0 hinner).hasFDerivAt
  have hz : (0 : V) ∈ c.target := h0 ▸ c.map_source h1
  have hi0 : c.symm 0 = (1 : G) := by rw [← h0, c.left_inv h1]
  have hid := hc.comp_symm_deriv hz
  erw [hi0] at hid
  exact hder.congr_fderiv hid

/-- The vertical derivative of the chart exponential is the derivative
of multiplication in its last variable. This formula uses only the actual
exponential homomorphism and the already computed identity derivative. -/
theorem chartExponentialCoordinates_hasFDerivAt
    (c : OpenPartialHomeomorph G V)
    (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (v : V) (hv : chartExponential (E := E) c v ∈ c.source) :
    HasFDerivAt (fun w => c (chartExponential (E := E) c w))
      (fderiv ℝ (fun y => c (c.symm (c (chartExponential (E := E) c v)) * c.symm y)) 0) v := by
  let f := fun w => c (chartExponential (E := E) c w)
  let m := fun y => c (c.symm (f v) * c.symm y)
  have hz : (0 : V) ∈ c.target := h0 ▸ c.map_source h1
  have hi0 : c.symm 0 = (1 : G) := by rw [← h0, c.left_inv h1]
  have hp : c.symm (f v) * c.symm 0 = chartExponential (E := E) c v := by
    rw [hi0, mul_one]
    exact c.left_inv hv
  have hleft : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun g : G => c.symm (f v) * g) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiable (by simp)
  have hmG : MDifferentiableAt (𝓘(ℝ, V)) (𝓘(ℝ, E))
      (fun y => c.symm (f v) * c.symm y) 0 :=
    (hleft (c.symm 0)).comp 0 (hc.mdifferentiableAt_symm hz)
  have hmC : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) c (c.symm (f v) * c.symm 0) := by
    rw [hp]
    exact hc.mdifferentiableAt hv
  have hm : HasFDerivAt m (fderiv ℝ m 0) 0 :=
    (hmC.comp 0 hmG).differentiableAt.hasFDerivAt
  have hf0 : f 0 = 0 := by dsimp only [f]; rw [chartExponential_zero, h0]
  have hfder := chartExponentialCoordinates_hasFDerivAt_zero c hc h1 h0
  have hsub : HasFDerivAt (fun w : V => w - v) (ContinuousLinearMap.id ℝ V) v :=
    (hasFDerivAt_id v).sub_const v
  have hinner : HasFDerivAt (fun w => f (w - v)) (ContinuousLinearMap.id ℝ V) v := by
    have hf' : HasFDerivAt f (ContinuousLinearMap.id ℝ V) (v - v) := by
      rw [sub_self]
      exact hfder
    exact (hf'.comp v (f := fun w : V => w - v) hsub).congr_fderiv (by ext w; rfl)
  have hm' : HasFDerivAt m (fderiv ℝ m 0) (f (v - v)) := by rw [sub_self, hf0]; exact hm
  have hcomposed : HasFDerivAt (fun w => m (f (w - v))) (fderiv ℝ m 0) v :=
    (hm'.comp v (f := fun w => f (w - v)) hinner).congr_fderiv (by ext w; rfl)
  have hcont : ContinuousAt (fun w => chartExponential (E := E) c (w - v)) v :=
    (chartExponential_mdifferentiable (E := E) c).continuous.continuousAt.comp
      (f := fun w : V => w - v) (x := v) (continuous_id.sub continuous_const).continuousAt
  have hmem : ∀ᶠ w in 𝓝 v, chartExponential (E := E) c (w - v) ∈ c.source :=
    hcont.preimage_mem_nhds (c.open_source.mem_nhds (by simpa only [sub_self, chartExponential_zero] using h1))
  have heq : (fun w => m (f (w - v))) =ᶠ[𝓝 v] f := by
    filter_upwards [hmem] with w hw
    change c (c.symm (c (chartExponential (E := E) c v)) *
      c.symm (c (chartExponential (E := E) c (w - v)))) = c (chartExponential (E := E) c w)
    rw [c.left_inv hv, c.left_inv hw, ← chartExponential_add]
    congr 2
    abel
  exact hcomposed.congr_of_eventuallyEq heq.symm

end

/-!
The derivative of an identity-preserving map in a differentiable identity
chart is the actual native derivative conjugated by the inverse-chart
tangent map. This is a chain-rule computation in the native manifold.
-/

open scoped _root_.Manifold ContDiff

variable {E V G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]

theorem chartEndomorphism_derivative
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (k : G → G) (hk : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) k 1) (hk1 : k 1 = 1)
    (v : V) :
    chartTangentMap (E := E) c (fderiv ℝ (fun y => c (k (c.symm y))) 0 v) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) k 1 (chartTangentMap (E := E) c v) := by
  have hz : (0 : V) ∈ c.target := h0 ▸ c.map_source h1
  have hi0 : c.symm 0 = (1 : G) := by rw [← h0, c.left_inv h1]
  have hkinner : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) k (c.symm 0) := by rw [hi0]; exact hk
  have hcouter : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) c (k (c.symm 0)) := by
    rw [hi0, hk1]
    exact hc.mdifferentiableAt h1
  have hinner := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    (0 : V) hkinner (hc.mdifferentiableAt_symm hz)
  have houter := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, V))
    (0 : V) hcouter (hkinner.comp 0 (hc.mdifferentiableAt_symm hz))
  rw [hinner, mfderiv_eq_fderiv] at houter
  have h := congrArg (fun D : V →L[ℝ] V => D v) houter
  change fderiv ℝ (fun y => c (k (c.symm y))) 0 v =
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, V)) c (k (c.symm 0))
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) k (c.symm 0)
        (chartTangentMap (E := E) c v)) at h
  erw [hi0, hk1] at h
  have hid := hc.symm_comp_deriv h1
  rw [h0] at hid
  rw [h]
  exact congrArg (fun D : E →L[ℝ] E =>
    D (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) k 1 (chartTangentMap (E := E) c v))) hid

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian
