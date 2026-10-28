import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothChartTangent
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Regular Chart Tangent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularChartTangent.Constructions

noncomputable section

/-!
# DegreeTwo: point derivations in any native regular affine chart

The transition into a regular chart is analytic because its coordinates
are regular fractions. Differentiating evaluation through that transition
transfers the realized derivation to the prescribed native chart.
-/

open scoped ContDiff _root_.Topology
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

variable {S : Type*} [CommRing S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- Every point derivation is realized in any prescribed regular affine
chart, rather than only the auxiliary standard-smooth chart. -/
theorem exists_tangent_in_regular_chart {k : ℕ}
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin k → ℂ))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S k) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxf : x ∈ f.source) :
    letI := x.toRingHom.toAlgebra
    ∀ δ : Derivation ℂ S ℂ, ∃ w : Fin k → ℂ,
      ∀ a : S, fderiv ℂ (fun z => f.symm z a) (f x) w = δ a := by
  let := x.toRingHom.toAlgebra
  intro δ
  obtain ⟨g, n, m, P, e, v, hxe, hi, hv⟩ := SmoothChartTangent.Constructions.exists_smoothAffine_chart_realizing_derivation x δ
  obtain ⟨b, hb, hcoords⟩ := hf.2
  let r := e.symm.trans f
  have hxr : e x ∈ r.source := by
    refine ⟨e.map_source hxe, ?_⟩
    change e.symm (e x) ∈ f.source
    rwa [e.left_inv hxe]
  have hrx : r (e x) = f x := by
    change f (e.symm (e x)) = f x
    rw [e.left_inv hxe]
  have ht : ContDiffAt ℂ ω r (e x) :=
    (ComplexPoints.Analytic.SmoothSchemeManifold.contDiffOn_affineChartTransition e f hi b hb hcoords).contDiffAt
      (r.open_source.mem_nhds hxr)
  let w := fderiv ℂ r (e x) v
  refine ⟨w, ?_⟩
  intro a
  have hd : DifferentiableAt ℂ (fun z => f.symm z a) (r (e x)) := by
    rw [hrx]
    exact (hf.1 a).differentiableOn (by simp) |>.differentiableAt
      (f.open_target.mem_nhds (f.map_source hxf))
  have heq : (fun z => e.symm z a) =ᶠ[𝓝 (e x)]
      (fun z => f.symm (r z) a) := by
    filter_upwards [r.open_source.mem_nhds hxr] with z hz
    change e.symm z a = f.symm (f (e.symm z)) a
    have hzs : e.symm z ∈ f.source := hz.2
    rw [f.left_inv hzs]
  have hc := fderiv_comp (e x) hd (ht.differentiableAt (by simp))
  have hcalc : fderiv ℂ (fun z => e.symm z a) (e x) v =
      fderiv ℂ (fun z => f.symm z a) (f x) w := by
    rw [heq.fderiv_eq]
    change fderiv ℂ ((fun z => f.symm z a) ∘ r) (e x) v = _
    rw [hc, hrx]
    rfl
  exact hcalc.symm.trans (hv a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularChartTangent.Constructions
