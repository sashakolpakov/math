import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AnalyticDerivation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EtaleDerivation

/-! # Smooth Chart Tangent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothChartTangent.Constructions

noncomputable section

/-!
# DegreeTwo: tangent realization on every smooth affine complex point space

A principal standard-smooth neighborhood carries the point derivation via
the actual étale differential base change. Its chart then lifts through the
genuine open embedding of localized complex points.
-/

open scoped ContDiff _root_.Topology

variable {S : Type*} [CommRing S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- Every point derivation on a smooth affine algebra is realized in an
actual analytic chart, with equality on every original regular function. -/
theorem exists_smoothAffine_chart_realizing_derivation (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    letI := x.toRingHom.toAlgebra
    ∀ δ : Derivation ℂ S ℂ,
    ∃ (g : S) (n m : ℕ)
      (P : Algebra.SubmersivePresentation ℂ (Localization.Away g) (Fin n) (Fin m))
      (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
      (v : ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ),
      x ∈ e.source ∧
      (∀ a : S, ContDiffOn ℂ ω (fun z => e.symm z a) e.target) ∧
      (∀ a : S, fderiv ℂ (fun z => e.symm z a) (e x) v = δ a) := by
  let := x.toRingHom.toAlgebra
  intro δ
  obtain ⟨g, hg, n, m, P, _⟩ := Foundations.Scheme.SmoothComplexPoint.Algebraic.smooth_point_exists_submersive_presentation x
  let T := Localization.Away g
  let y := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg
  let : Algebra T ℂ := y.toRingHom.toAlgebra
  let : IsScalarTower ℂ T ℂ := IsScalarTower.of_algHom y
  let : IsScalarTower S T ℂ := IsScalarTower.of_algebraMap_eq (fun a => by
    exact (DFunLike.congr_fun (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x g hg) a).symm)
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
  let ε := EtaleDerivation.Constructions.etaleExtendDerivation ℂ S T ℂ δ
  obtain ⟨e₀, hy, hf, hi, ht⟩ := AnalyticDerivation.Constructions.exists_standardSmooth_chart_realizing_derivations
    P y (fun _ => rfl)
  let ιg := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g
  have hιg : Topology.IsOpenEmbedding ιg :=
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g
  let e := e₀.lift_openEmbedding hιg
  have hιy : ιg y = x := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x g hg
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
    rw [hex, ht, EtaleDerivation.Constructions.etaleExtendDerivation_algebraMap]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothChartTangent.Constructions
