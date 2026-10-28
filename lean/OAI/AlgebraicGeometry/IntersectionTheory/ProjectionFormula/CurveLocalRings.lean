import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

/-! # Curve Local Rings -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveLocalRings

noncomputable section

/-! Normal integral curves have valuation rings at every point, including
the generic point. The dimension bound follows from the actual affine
coordinate rings and their proved finite-type dimension formula. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

theorem coheight_le_dimension {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    coheight x ≤ (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f : ℕ∞) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let x' : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨x'⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  have h := (hU.primeIdealOf x').asIdeal.height_le_ringKrullDim_of_isPrime
  rw [idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion hU.fromSpec,
    hU.fromSpec_primeIdealOf, DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg k Γ(X, U),
    ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU] at h
  exact WithBot.coe_le_coe.mp h

theorem normal_local_valuation (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Ring.KrullDimLE 1 R] : ValuationRing R := by
  let : Ring.DimensionLEOne R := ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  let : IsDedekindDomain R :=
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }
  by_cases hf : IsField R
  · let : Field R := hf.toField
    infer_instance
  · have h : IsDiscreteValuationRing R ↔ IsDedekindDomain R := (IsDiscreteValuationRing.TFAE R hf).out 1 3
    let : IsDiscreteValuationRing R := h.mpr inferInstance
    infer_instance

/-- Every point of a normal curve admits the valuation-ring argument;
the generic-point local ring is included automatically. -/
theorem stalk_valuation {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f ≤ 1) (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] : ValuationRing (X.presheaf.stalk x) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hx : coheight x ≤ 1 := (coheight_le_dimension f x).trans (by exact_mod_cast hdim)
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx
  exact normal_local_valuation (X.presheaf.stalk x)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveLocalRings
