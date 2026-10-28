import OAI.Geometry.ComplexTorus.RiemannProjectivity.ImageChartsIn
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularProjectionIs
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts

/-! # Cone Tangent F -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent

/-!
# RiemannProjectivity: tangent spaces of the projective cone

In a projective affine chart, a cone point is the chart's normalized vector
times a nonzero scalar. The scalar direction together with the tangent of
the projective embedding gives an injective cone derivative.
-/

open Set

variable {n : ℕ}

def insertCoordinate (i : Fin (n + 1)) :
    (ℂ × (Fin n → ℂ)) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
  ({ Fin.insertNthEquiv (fun _ => ℂ) i with
      map_add' := by
        intro x y
        ext j
        refine Fin.succAboveCases i ?_ (fun l => ?_) j <;>
          simp [Fin.insertNthEquiv]
      map_smul' := by
        intro c x
        ext j
        refine Fin.succAboveCases i ?_ (fun l => ?_) j <;>
          simp [Fin.insertNthEquiv] } : (ℂ × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin (n + 1) → ℂ)).toContinuousLinearEquiv

@[simp]
theorem insertCoordinate_apply (i : Fin (n + 1)) (p : ℂ × (Fin n → ℂ)) :
    insertCoordinate i p = i.insertNth p.1 p.2 := rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def parameterization (i : Fin (n + 1)) (r : V → Fin n → ℂ) (p : V × ℂ) : Fin (n + 1) → ℂ :=
  insertCoordinate i (p.2, p.2 • r p.1)

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem dehomogenize_parameterization (i : Fin (n + 1)) (r : V → Fin n → ℂ)
    (z : V) {c : ℂ} (hc : c ≠ 0) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i (parameterization i r (z, c)) = r z := by
  ext j
  simp only [AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize, parameterization, insertCoordinate_apply,
    Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul]
  exact mul_div_cancel_left₀ _ hc

theorem insertCoordinate_dehomogenize (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ)
    (hi : v i ≠ 0) : insertCoordinate i (v i, v i • AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v) = v := by
  ext j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simp
  · simp only [insertCoordinate_apply, Fin.insertNth_apply_succAbove, Pi.smul_apply,
      smul_eq_mul, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize]
    field_simp

def tangentMap (i : Fin (n + 1)) (r : V → Fin n → ℂ) (z : V) :
    (V × ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  (insertCoordinate i).toContinuousLinearMap.comp
    ((ContinuousLinearMap.snd ℂ V ℂ).prod
      ((fderiv ℂ r z).comp (ContinuousLinearMap.fst ℂ V ℂ) +
        (ContinuousLinearMap.snd ℂ V ℂ).smulRight (r z)))

theorem tangentMap_apply (i : Fin (n + 1)) (r : V → Fin n → ℂ) (z : V) (p : V × ℂ) :
    tangentMap i r z p = i.insertNth p.2 (fderiv ℂ r z p.1 + p.2 • r z) := rfl

theorem hasFDerivAt_parameterization (i : Fin (n + 1)) {r : V → Fin n → ℂ} {z : V}
    (hr : DifferentiableAt ℂ r z) :
    HasFDerivAt (parameterization i r) (tangentMap i r z) (z, 1) := by
  have hfst := (hasFDerivAt_fst (𝕜 := ℂ) (p := (z, (1 : ℂ))))
  have hsnd := (hasFDerivAt_snd (𝕜 := ℂ) (p := (z, (1 : ℂ))))
  have hrp := hr.hasFDerivAt.comp (z, (1 : ℂ)) hfst
  have hsmul := hsnd.smul hrp
  have hpair := hsnd.prodMk hsmul
  simpa only [parameterization, tangentMap, Prod.snd, one_smul] using!
    (insertCoordinate i).hasFDerivAt.comp (z, (1 : ℂ)) hpair

theorem differentiableOn_parameterization (i : Fin (n + 1)) {r : V → Fin n → ℂ}
    {U : Set V} (hr : DifferentiableOn ℂ r U) :
    DifferentiableOn ℂ (parameterization i r) (U ×ˢ univ) := by
  have hsnd : DifferentiableOn ℂ (Prod.snd : V × ℂ → ℂ) (U ×ˢ univ) :=
    differentiable_snd.differentiableOn
  have hrp : DifferentiableOn ℂ (fun p : V × ℂ => r p.1) (U ×ˢ univ) :=
    hr.comp differentiable_fst.differentiableOn (fun p hp => hp.1)
  simpa only [parameterization, Function.comp_def] using!
    (insertCoordinate i).differentiable.comp_differentiableOn (hsnd.prodMk (hsnd.smul hrp))

theorem tangentMap_injective (i : Fin (n + 1)) {r : V → Fin n → ℂ} {z : V}
    (hr : Function.Injective (fderiv ℂ r z)) : Function.Injective (tangentMap i r z) := by
  apply (injective_iff_map_eq_zero (tangentMap i r z)).mpr
  intro p hp
  have hpi : p.2 = 0 := by
    have h := congrFun hp i
    simpa only [tangentMap_apply, Fin.insertNth_apply_same, Pi.zero_apply] using h
  have hfirst : fderiv ℂ r z p.1 = 0 := by
    ext j
    have h := congrFun hp (i.succAbove j)
    simpa only [tangentMap_apply, Fin.insertNth_apply_succAbove, hpi,
      zero_smul, add_zero, Pi.zero_apply] using h
  exact Prod.ext ((map_eq_zero_iff _ hr).mp hfirst) hpi

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem parameterization_mem_cone (i : Fin (n + 1))
    (g : V → Projectivization ℂ (Fin (n + 1) → ℂ)) (z : V)
    (hz : g z ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) (c : ℂ) :
    parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g w)) (z, c) ∈
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range g) := by
  by_cases hc : c = 0
  · subst c
    have heq : parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g w)) (z, 0) = 0 := by
      change insertCoordinate i (0, (0 : ℂ) • AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z)) = 0
      simpa only [zero_smul] using! (insertCoordinate i).map_zero
    rw [heq]
    exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.zero_mem_projectiveCone _
  · let v := parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g w)) (z, c)
    have hvi : v i ≠ 0 := by simpa only [v, parameterization, insertCoordinate_apply,
      Fin.insertNth_apply_same] using hc
    apply (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.mem_projectiveCone_iff_dehomogenize (range g) i v hvi).mpr
    have hde : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z) := by
      ext j
      simp only [AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize, v, parameterization, insertCoordinate_apply,
        Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul]
      exact mul_div_cancel_left₀ _ hc
    rw [hde, (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).left_inv hz]
    exact mem_range_self z

end Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent

namespace Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeLocalTopology

/-!
# RiemannProjectivity: local openness of the cone parametrization

An open quotient parametrization of a projectively embedded space remains
locally open after adjoining the nonzero scalar coordinate of its cone.
This ensures that inverse-function coordinates describe the entire cone
near a point, not just one parametrized subset.
-/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent

variable {V T : Type*} [TopologicalSpace V] [TopologicalSpace T] {n : ℕ}

/-- Every sufficiently nearby cone point has a parameter lift near the
given parameter, provided its scalar coordinate is nonzero. -/
theorem parameter_image_mem_nhds (p : V → T) (hp : IsOpenMap p)
    (f : T → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsEmbedding f)
    (i : Fin (n + 1)) (z : V) (c : ℂ) (hc : c ≠ 0)
    (hi : f (p z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v₀ : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv₀ : v₀.val = ConeTangent.parameterization i (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (p w))) (z, c))
    {D : Set (V × ℂ)} (hD : D ∈ 𝓝 (z, c)) :
    {v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) | ∃ w ∈ D,
      ConeTangent.parameterization i (fun u => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (p u))) w = v.val} ∈ 𝓝 v₀ := by
  obtain ⟨A, B, hA, hzA, hB, hcB, hAB⟩ := mem_nhds_prod_iff'.mp hD
  obtain ⟨O, hO, hpre⟩ := hf.isInducing.isOpen_iff.mp (hp A hA)
  have hfpO : f (p z) ∈ O := by
    change p z ∈ f ⁻¹' O
    rw [hpre]
    exact ⟨z, hzA, rfl⟩
  have hv₀i : v₀.val i = c := by
    rw [hv₀]
    simp only [ConeTangent.parameterization, ConeTangent.insertCoordinate_apply, Fin.insertNth_apply_same]
  have hv₀ne : v₀.val i ≠ 0 := by rwa [hv₀i]
  let J : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun v => (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val)
  have hJ₀ : J v₀ = f (p z) := by
    change (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v₀.val) = f (p z)
    rw [hv₀, ConeTangent.dehomogenize_parameterization i _ z hc, (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).left_inv hi]
  have hpatch : IsOpen {v : Fin (n + 1) → ℂ | v i ≠ 0} :=
    isOpen_ne_fun (continuous_apply i) continuous_const
  have hde : ContinuousAt (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i) v₀.val :=
    ((AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.differentiableOn_dehomogenize i _ hv₀ne).differentiableAt
      (hpatch.mem_nhds hv₀ne)).continuousAt
  have hinv : Continuous (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm := by
    apply continuousOn_univ.mp
    simpa only [AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_target] using (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).continuousOn_symm
  have hJ : ContinuousAt J v₀ :=
    hinv.continuousAt.comp (hde.comp continuous_subtype_val.continuousAt)
  have hcoord : Continuous (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => v.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  have hnearO : ∀ᶠ v in 𝓝 v₀, J v ∈ O :=
    hJ (hO.mem_nhds (hJ₀ ▸ hfpO))
  have hnearB : ∀ᶠ v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) in 𝓝 v₀, v.val i ∈ B :=
    hcoord.continuousAt (hB.mem_nhds (hv₀i ▸ hcB))
  have hnear0 : ∀ᶠ v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) in 𝓝 v₀, v.val i ≠ 0 :=
    (isOpen_ne_fun hcoord continuous_const).mem_nhds hv₀ne
  filter_upwards [hnearO, hnearB, hnear0] with v hvO hvB hvi
  obtain ⟨t, ht⟩ := (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.mem_projectiveCone_iff_dehomogenize (range f) i v.val hvi).mp v.property
  have htA : t ∈ p '' A := by
    rw [← hpre]
    change f t ∈ O
    rw [ht]
    exact hvO
  obtain ⟨w, hwA, hwt⟩ := htA
  refine ⟨(w, v.val i), hAB ⟨hwA, hvB⟩, ?_⟩
  have hratio : AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (p w)) = AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val := by
    rw [hwt, ht]
    exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).right_inv (by rw [AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_target]; trivial)
  change ConeTangent.insertCoordinate i (v.val i, v.val i • AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (p w))) = v.val
  rw [hratio]
  exact ConeTangent.insertCoordinate_dehomogenize i v.val hvi

end Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeLocalTopology

end

end OAI
