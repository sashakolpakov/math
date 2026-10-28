import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizerPrimeSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AffineSectionCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorSmooth

/-! # Section Prime Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionPrimeSupport.Constructions

noncomputable section

/-!
# DegreeTwo: an actual divisor parameter cuts out its actual prime support

The DVR ideal equality descends to one affine principal neighborhood.
Evaluation of the section is then zero exactly on the scheme closure
of the original codimension-one point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- On a genuine principal neighborhood through the divisor's generic
point, its regular parameter vanishes precisely on that prime divisor. -/
theorem section_uniformizer_prime_support_neighborhood (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [IsIntegral X.carrier] (U : X.carrier.Opens) (hU : IsAffineOpen U)
    (z : X.carrier) (hzU : z ∈ U) (hz : Order.coheight z = 1)
    (p : Γ(X.carrier, U)) (hp : Irreducible (X.carrier.presheaf.germ U z hzU p)) :
    ∃ b : Γ(X.carrier, U), IsUnit (X.carrier.presheaf.germ U z hzU b) ∧
      ∀ y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U, DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U b y ≠ 0 →
        (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0 ↔
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y.val ∈ closure ({z} : Set X.carrier)) := by
  let : Nonempty U := ⟨⟨z, hzU⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.structureMap U
  let : Smooth X.structureMap := X.smooth
  let : Algebra.Smooth ℂ Γ(X.carrier, U) := Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth X.structureMap U hU
  let : IsNoetherianRing Γ(X.carrier, U) := Algebra.FiniteType.isNoetherianRing ℂ Γ(X.carrier, U)
  let := X.carrier.presheaf.algebra_section_stalk ⟨z, hzU⟩
  let := hU.isLocalization_stalk ⟨z, hzU⟩
  let P := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
  let : IsDiscreteValuationRing (X.carrier.presheaf.stalk z) :=
    SmoothDVR.Constructions.smoothScheme_stalk_isDiscreteValuationRing X.structureMap z hz
  let : IsDomain (Localization.AtPrime P) :=
    Foundations.Scheme.SmoothLocalDomain.isDomain_localizationAtPrime_of_smooth ℂ Γ(X.carrier, U) P
  let e : X.carrier.presheaf.stalk z ≃ₐ[Γ(X.carrier, U)] Localization.AtPrime P :=
    IsLocalization.algEquiv P.primeCompl (X.carrier.presheaf.stalk z) (Localization.AtPrime P)
  let : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hp' := hp.map e.toMulEquiv
  change Irreducible (e (algebraMap Γ(X.carrier, U) (X.carrier.presheaf.stalk z) p)) at hp'
  rw [e.commutes] at hp'
  obtain ⟨b, hb, hsupport⟩ := UniformizerPrimeSupport.Constructions.uniformizer_prime_support_neighborhood P p hp'
  refine ⟨b, IsLocalization.map_units (X.carrier.presheaf.stalk z) (⟨b, hb⟩ : P.primeCompl), ?_⟩
  intro y hyb
  let E := AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph X U hU
  let a := E.symm y
  have heval (r : Γ(X.carrier, U)) : a r = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U r y := by
    have h := AffineSectionCoordinates.Constructions.affineSectionPointHomeomorph_evaluation X U hU a r
    change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U r (E (E.symm y)) = a r at h
    rw [E.apply_symm_apply] at h
    exact h.symm
  have hbker : b ∉ RingHom.ker a.toRingHom := by
    change a b ≠ 0
    rwa [heval b]
  have h := hsupport (RingHom.ker a.toRingHom) (RingHom.ker_isPrime a.toRingHom) hbker
  change a p = 0 ↔ P ≤ RingHom.ker a.toRingHom at h
  rw [heval p] at h
  have hc := AffineSectionCoordinates.Constructions.affineSectionPoint_mem_pointClosure_iff X U hU ⟨z, hzU⟩ a
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (E (E.symm y)).val ∈ closure ({z} : Set X.carrier) ↔
    P ≤ RingHom.ker a.toRingHom at hc
  rw [E.apply_symm_apply] at hc
  exact h.trans hc.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SectionPrimeSupport.Constructions
