import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AnalyticDerivation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EtaleDerivation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Tangent Realization -/

namespace OAI.RepresentationTheory.Theta.Geometric.TangentRealization

noncomputable section

/- Adapted from the proved SmoothChartTangent and RegularChartTangent,
with current local-instance syntax and the same geometric construction. -/

/-!
# DegreeTwo: tangent realization on every smooth affine complex point space

A principal standard-smooth neighborhood carries the point derivation via
the actual étale differential base change. Its chart then lifts through the
genuine open embedding of localized complex points.
-/

open scoped ContDiff _root_.Topology
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

section

variable {S : Type*} [CommRing S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- Every point derivation on a smooth affine algebra is realized in an
actual analytic chart, with equality on every original regular function. -/
theorem exists_smoothAffine_chart_realizing_derivation (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    letI := x.toRingHom.toAlgebra
    ∀ δ : Derivation ℂ S ℂ,
    ∃ (g : S) (n m : ℕ)
      (P : Algebra.SubmersivePresentation ℂ (Localization.Away g) (Fin n) (Fin m))
      (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
      (v : AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ),
      x ∈ e.source ∧
      (∀ a : S, ContDiffOn ℂ ω (fun z => e.symm z a) e.target) ∧
      (∀ a : S, fderiv ℂ (fun z => e.symm z a) (e x) v = δ a) := by
  let := x.toRingHom.toAlgebra
  intro δ
  obtain ⟨g, hg, n, m, P, _⟩ := AlgebraicGeometry.Foundations.Scheme.SmoothComplexPoint.Algebraic.smooth_point_exists_submersive_presentation x
  let T := Localization.Away g
  let y := AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg
  let : Algebra T ℂ := y.toRingHom.toAlgebra
  let : IsScalarTower ℂ T ℂ := IsScalarTower.of_algHom y
  let : IsScalarTower S T ℂ := IsScalarTower.of_algebraMap_eq (fun a => by
    exact (DFunLike.congr_fun (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x g hg) a).symm)
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
  let ε := AlgebraicGeometry.HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions.etaleExtendDerivation ℂ S T ℂ δ
  obtain ⟨e₀, hy, hf, hi, ht⟩ := AlgebraicGeometry.HodgeConjecture.DegreeTwo.AnalyticDerivation.Constructions.exists_standardSmooth_chart_realizing_derivations
    P y (fun _ => rfl)
  let ιg := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g
  have hιg : Topology.IsOpenEmbedding ιg :=
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g
  let e := e₀.lift_openEmbedding hιg
  have hιy : ιg y = x := AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x g hg
  have hx : x ∈ e.source := ⟨y, hy, hιy⟩
  have hex : e x = e₀ y := by
    rw [← hιy]
    exact e₀.lift_openEmbedding_apply hιg
  refine ⟨g, n, m, P, e, (fun i => ε (P.val i.val)), hx, ?_, ?_⟩
  · intro a
    exact hi (algebraMap S T a)
  · intro a
    change fderiv ℂ (fun z => e₀.symm z (algebraMap S T a)) (e x)
      (fun i => ε (P.val i.val)) = δ a
    rw [hex, ht, AlgebraicGeometry.HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions.etaleExtendDerivation_algebraMap]

end

/-!
# DegreeTwo: point derivations in any native regular affine chart

The transition into a regular chart is analytic because its coordinates
are regular fractions. Differentiating evaluation through that transition
transfers the realized derivation to the prescribed native chart.
-/

variable {S : Type*} [CommRing S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- Every point derivation is realized in any prescribed regular affine
chart, rather than only the auxiliary standard-smooth chart. -/
theorem exists_tangent_in_regular_chart {k : ℕ}
    (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin k → ℂ))
    (hf : f ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S k) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxf : x ∈ f.source) :
    letI := x.toRingHom.toAlgebra
    ∀ δ : Derivation ℂ S ℂ, ∃ w : Fin k → ℂ,
      ∀ a : S, fderiv ℂ (fun z => f.symm z a) (f x) w = δ a := by
  let := x.toRingHom.toAlgebra
  intro δ
  obtain ⟨g, n, m, P, e, v, hxe, hi, hv⟩ := exists_smoothAffine_chart_realizing_derivation x δ
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
    (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.contDiffOn_affineChartTransition e f hi b hb hcoords).contDiffAt
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

end OAI.RepresentationTheory.Theta.Geometric.TangentRealization
