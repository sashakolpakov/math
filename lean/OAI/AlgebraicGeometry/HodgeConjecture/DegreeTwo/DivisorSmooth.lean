import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizerSmooth
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorEquations

/-! # Divisor Smooth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorSmooth.Constructions

noncomputable section

/-!
# DegreeTwo: smooth hypersurface neighborhoods for actual divisor parameters

The affine stalk comparison carries the regular section's uniformizer to
the genuine prime localization. Smoothness of its principal quotient then
gives a neighborhood element which is a unit at the original scheme point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u

/-- The principal hypersurface of an actual regular parameter has a smooth
affine neighborhood through the original codimension-one scheme point. -/
theorem smooth_uniformizer_section_neighborhood {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [Smooth f] (U : X.Opens) (hU : U ∈ X.affineOpens)
    (x : X) (hxU : x ∈ U) (hx : coheight x = 1) (p : Γ(X, U))
    (hp : Irreducible (X.presheaf.germ U x hxU p)) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    ∃ b : Γ(X, U), IsUnit (X.presheaf.germ U x hxU b) ∧
      Algebra.Smooth K (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b)) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth f U hU
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let := hU.isLocalization_stalk ⟨x, hxU⟩
  let P := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : IsDiscreteValuationRing (X.presheaf.stalk x) := SmoothDVR.Constructions.smoothScheme_stalk_isDiscreteValuationRing f x hx
  let : IsDomain (Localization.AtPrime P) :=
    Foundations.Scheme.SmoothLocalDomain.isDomain_localizationAtPrime_of_smooth K Γ(X, U) P
  let e : (X.presheaf.stalk x) ≃ₐ[Γ(X, U)] Localization.AtPrime P :=
    IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk x) (Localization.AtPrime P)
  let : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hp' := hp.map e.toMulEquiv
  change Irreducible (e (algebraMap Γ(X, U) (X.presheaf.stalk x) p)) at hp'
  rw [e.commutes] at hp'
  obtain ⟨b, hb, hsm⟩ := UniformizerSmooth.Constructions.uniformizer_hypersurface_smooth_neighborhood P K p hp'
  exact ⟨b, IsLocalization.map_units (X.presheaf.stalk x) (⟨b, hb⟩ : P.primeCompl), hsm⟩

/-- The actual section equation with its algebraic multiplicity can be
chosen together with a smooth hypersurface neighborhood through the point. -/
theorem rationalSection_smooth_local_equation {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]
    (x : X.carrier) (hx : coheight x = 1) (i : X.carrier) (hxi : x ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : U ∈ X.carrier.affineOpens) (hxU : x ∈ U)
      (_ : U ≤ L.trivializingOpen i) (p : Γ(X.carrier, U)) (v : Γ(X.carrier, U)ˣ) (b : Γ(X.carrier, U)),
      Irreducible (X.carrier.presheaf.germ U x hxU p) ∧
      IsUnit (X.carrier.presheaf.germ U x hxU b) ∧
      (letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.structureMap U
       Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b))) ∧
      letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      (L.rationalSectionCoordinate i : X.carrier.functionField) =
        X.carrier.germToFunctionField U v *
          (X.carrier.germToFunctionField U p) ^ (L.rationalSectionOrder x) := by
  let : Smooth X.structureMap := X.smooth
  obtain ⟨U, hU, hxU, hUi, p, v, hp, he⟩ := DivisorEquations.Constructions.rationalSection_local_equation L x hx i hxi
  obtain ⟨b, hb, hsm⟩ := smooth_uniformizer_section_neighborhood X.structureMap U hU x hxU hx p hp
  exact ⟨U, hU, hxU, hUi, p, v, b, hp, hb, hsm, he⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorSmooth.Constructions
