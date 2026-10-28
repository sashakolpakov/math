import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Exponential Complex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialComplex.Constructions.Exponential

noncomputable section

/-!
# DegreeTwo: complex differentiability of the constructed exponential

The real exponential has identity differential at zero. In complex coordinates
this differential is complex linear, so it is a complex derivative. The group
law transports this derivative to every point.
-/

open _root_.Manifold
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] [TopologicalSpace C] [ChartedSpace E C] [CommGroup C]
  [LieGroup (𝓘(ℝ, E)) ∞ C] [LieGroup (𝓘(ℂ, E)) ∞ C] [T2Space C]

local instance : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E

omit [LieGroup (𝓘(ℂ, E)) ∞ C] in
/-- The chart expression of the exponential has the complex identity as its
derivative at zero; the real derivative is the restriction of this map. -/
theorem hasFDerivAt_chart_expMap_zero_complex :
    HasFDerivAt (extChartAt (𝓘(ℂ, E)) (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) 0) ∘ ExponentialM.Constructions.Exponential.expMap (E := E) (C := C))
      (ContinuousLinearMap.id ℂ E) (0 : E) := by
  have hchart := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
    (mem_chart_source E (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) 0))).hasMFDerivAt
  have h := hchart.comp 0 (ExponentialM.Constructions.Exponential.hasMFDerivAt_expMap_zero (E := E) (C := C))
  have hr : HasFDerivAt
      (extChartAt (𝓘(ℂ, E)) (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) 0) ∘ ExponentialM.Constructions.Exponential.expMap (E := E) (C := C))
      (ContinuousLinearMap.id ℝ E) (0 : E) := by
    apply HasMFDerivAt.hasFDerivAt
    apply h.congr_mfderiv
    rw [mfderiv_extChartAt_self]
    ext x
    rfl
  exact hasFDerivAt_of_restrictScalars ℝ hr rfl

omit [LieGroup (𝓘(ℂ, E)) ∞ C] in
/-- The constructed real exponential is complex differentiable at zero. -/
theorem expMap_complex_mdifferentiableAt_zero :
    MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, E)) (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) 0 := by
  apply mdifferentiableAt_iff_target.mpr
  exact ⟨ExponentialM.Constructions.Exponential.expMap_continuous.continuousAt,
    hasFDerivAt_chart_expMap_zero_complex.differentiableAt.mdifferentiableAt⟩

/-- Holomorphic group translation transports complex differentiability at
zero to every point of the tangent space. -/
theorem expMap_complex_mdifferentiable :
    MDifferentiable (𝓘(ℂ, E)) (𝓘(ℂ, E)) (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) := by
  intro v
  have hs : MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, E)) (fun x : E => x - v) v :=
    ((differentiableAt_id : DifferentiableAt ℂ (fun x : E => x) v).sub
      (differentiableAt_const v)).mdifferentiableAt
  have h₀ : MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, E))
      (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) (v - v) := by
    simpa only [sub_self] using expMap_complex_mdifferentiableAt_zero (E := E) (C := C)
  have hm : MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, E))
      (fun y : C => ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) v * y) (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) (v - v)) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiableAt (by simp)
  have h := hm.comp v (h₀.comp (f := fun x : E => x - v) v hs)
  have heq : (fun y : C => ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) v * y) ∘
      (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) ∘ (fun x : E => x - v)) = ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) := by
    funext x
    dsimp only [Function.comp_apply]
    rw [← ExponentialM.Constructions.Exponential.expMap_add]
    congr 1
    abel
  rwa [heq] at h

theorem localInverse_complex_mdifferentiableAt
    (e : OpenPartialHomeomorph E C) (he₀ : (0 : E) ∈ e.source)
    (he : (e : E → C) = ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) :
    MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, E)) e.symm
      (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) 0) := by
  let f := ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)
  let c := chartAt E (f 0)
  let k := e.trans c
  have hc₀ : f 0 ∈ c.source := mem_chart_source E (f 0)
  have hk₀ : (0 : E) ∈ k.source := by
    refine ⟨he₀, ?_⟩
    change e 0 ∈ c.source
    rw [he]
    exact hc₀
  have hkfun : (k : E → E) = extChartAt (𝓘(ℂ, E)) (f 0) ∘ f := by
    funext x
    change c (e x) = c (f x)
    rw [he]
  have hkval : k 0 = c (f 0) := congrArg c (congrFun he 0)
  have hka : c (f 0) ∈ k.target := hkval ▸ k.map_source hk₀
  have hki : k.symm (c (f 0)) = 0 := by
    rw [← hkval]
    exact k.left_inv hk₀
  have hkderiv : HasFDerivAt k
      (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E) (k.symm (c (f 0))) := by
    rw [hki, hkfun]
    exact hasFDerivAt_chart_expMap_zero_complex
  have hi := (k.hasFDerivAt_symm hka hkderiv).differentiableAt.mdifferentiableAt
  have hc : MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, E)) c (f 0) :=
    mdifferentiableAt_extChartAt hc₀
  have hh := hi.comp (f 0) hc
  have heq : (e.symm : C → E) =ᶠ[𝓝 (f 0)] k.symm ∘ c := by
    filter_upwards [c.open_source.mem_nhds hc₀] with y hy
    change e.symm y = e.symm (c.symm (c y))
    rw [c.left_inv hy]
  exact heq.mdifferentiableAt_iff.mpr hh

/-- The exponential quotient homeomorphism is holomorphic, because its
composition with the lattice projection is the holomorphic exponential. -/
theorem expQuotientHomeomorph_mdifferentiable [ConnectedSpace C] :
    MDifferentiable (𝓘(ℂ, E)) (𝓘(ℂ, E))
      (ExponentialLocal.Constructions.Exponential.expQuotientHomeomorph (E := E) (C := C)) :=
  Torus.Constructions.LatticeQuotient.mdifferentiable_of_projection
    (ExponentialLocal.Constructions.Exponential.expLattice (E := E) (C := C)) _ expMap_complex_mdifferentiable

theorem expQuotientHomeomorph_symm_mdifferentiable [ConnectedSpace C] :
    MDifferentiable (𝓘(ℂ, E)) (𝓘(ℂ, E))
      (ExponentialLocal.Constructions.Exponential.expQuotientHomeomorph (E := E) (C := C)).symm := by
  let f := ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)
  let q := ExponentialLocal.Constructions.Exponential.expQuotientHomeomorph (E := E) (C := C)
  let Λ := ExponentialLocal.Constructions.Exponential.expLattice (E := E) (C := C)
  intro y
  obtain ⟨v, rfl⟩ := ExponentialLocal.Constructions.Exponential.expMap_surjective (E := E) (C := C) y
  obtain ⟨e, he₀, he⟩ := ExponentialLocal.Constructions.Exponential.exists_expMap_localHomeomorph_zero (E := E) (C := C)
  let t : C → C := fun z => (f v)⁻¹ * z
  have ht : MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, E)) t (f v) :=
    (contMDiff_mul_left (n := ∞)).mdifferentiableAt (by simp)
  have ht₀ : t (f v) = f 0 := by
    change (f v)⁻¹ * f v = ExponentialM.Constructions.Exponential.exp (G := C) 0
    rw [inv_mul_cancel, ExponentialM.Constructions.Exponential.exp_zero]
  have hl := localInverse_complex_mdifferentiableAt e he₀ he
  have hlt := hl.comp_of_eq (f v) ht ht₀
  have hv : MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, E))
      (fun z : C => v + e.symm (t z)) (f v) :=
    mdifferentiableAt_const.add hlt
  have hp : MDifferentiable (𝓘(ℂ, E)) (𝓘(ℂ, E))
      (QuotientAddGroup.mk : E → Torus.Constructions.LatticeQuotient.Point Λ) :=
    (Torus.Constructions.LatticeQuotient.projection_contMDiff Λ).mdifferentiable (by simp)
  have h := (hp (v + e.symm (t (f v)))).comp (f v) hv
  have he_target : f 0 ∈ e.target := by simpa only [he] using e.map_source he₀
  have hn : ∀ᶠ z in 𝓝 (f v), t z ∈ e.target :=
    ht.continuousAt.preimage_mem_nhds (ht₀.symm ▸ e.open_target.mem_nhds he_target)
  have heq : (q.symm : C → Torus.Constructions.LatticeQuotient.Point Λ) =ᶠ[𝓝 (f v)]
      (fun z => QuotientAddGroup.mk (v + e.symm (t z))) := by
    filter_upwards [hn] with z hz
    apply q.injective
    rw [q.apply_symm_apply]
    change z = ExponentialM.Constructions.Exponential.expMap (C := C) (v + e.symm (t z))
    rw [ExponentialM.Constructions.Exponential.expMap_add]
    change z = f v * f (e.symm (t z))
    have hinv : f (e.symm (t z)) = t z := by
      change ExponentialM.Constructions.Exponential.expMap (C := C) (e.symm (t z)) = t z
      rw [← he]
      exact e.right_inv hz
    rw [hinv]
    change z = f v * ((f v)⁻¹ * z)
    simp
  exact heq.mdifferentiableAt_iff.mpr h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialComplex.Constructions.Exponential
