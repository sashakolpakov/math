import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CurvePointDimension

/-! # Local Valuation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.LocalValuation.BundleCycles

noncomputable section

section

/-! Normal local rings of dimension at most one are valuation rings. -/

open _root_.AlgebraicGeometry

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

end

/-! Normal stalks over the generic point of a relative curve are valuation rings. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem relativeCurve_stalkValuation {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] (f : X ⟶ Y) (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (x : X) (hx : f x = genericPoint Y) [IsIntegrallyClosed (X.presheaf.stalk x)] :
    ValuationRing (X.presheaf.stalk x) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    krullDimLE_of_coheight_le (Relative.CurvePointDimension.BundleCycles.relativeCurve_coheight_le_one f gY hdim x hx)
  exact normal_local_valuation _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.LocalValuation.BundleCycles
