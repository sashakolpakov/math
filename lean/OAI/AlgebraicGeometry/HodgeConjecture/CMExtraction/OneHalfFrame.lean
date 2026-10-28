import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RootRatio
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FrameRoot

/-! # One Half Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneHalfFrame

noncomputable section

/-! The one-line and native half-frames differ by one fixed nonzero
scalar, determined at the native origin. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

namespace Quadratic

theorem ballHolomorphic_continuous {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : RepresentationTheory.Theta.Adelic.BallNatural.Ball → V) (hf : RepresentationTheory.Theta.Adelic.BallGeometryData.BallHolomorphic f) : Continuous f := by
  have hc := continuousOn_iff_continuous_domRestrict.mp hf.continuousOn
  exact hc.congr (fun z => by simp only [Set.domRestrict_apply, dite_eq_left z.property]; rfl)

theorem comparison_halfFrame_sq
    {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
    {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
    {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    B.halfFrame z ^ 2 = OneFrameDeterminant.Quadratic.comparisonFrameDet B z :=
  (hGeometry.2.2.2.2.2.1 z).2

end Quadratic

namespace Multiplicity

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem nativeOne_halfFrame_constant
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) :
    let e := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
    let he := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord
    let R := Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he
    ∀ z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain},
      B.halfFrame (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z) =
        (B.halfFrame (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ (Intrinsic.PeriodDomain.Multiplicity.nativeOrigin E P hP)) /
          R (Intrinsic.PeriodDomain.Multiplicity.nativeOrigin E P hP)) * R z := by
  dsimp only
  let e := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
  let he := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord
  let R := Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he
  let f := fun z => B.halfFrame (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z)
  let C := ∏ i : Fin s × Fin 3, OneComponentScales.Multiplicity.nativeOneFrameScale E P v i.1 i.2
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => OneComponentScales.Multiplicity.nativeOneFrameScale_ne_zero E P hP hμ v i.1 i.2)
  have hsquare (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) : f z ^ 2 = C⁻¹ * R z ^ 2 := by
    have hd : f z ^ 2 * C = R z ^ 2 := by
      rw [Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot_sq]
      exact (congrArg (fun c : ℂ => c * C)
        (Quadratic.comparison_halfFrame_sq B hGeometry (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z))).trans
          (OneFrameDeterminant.Multiplicity.nativeOne_lowerFrame_det E P hP hμ hs v hv B hCoord hGeometry z)
    calc
      f z ^ 2 = R z ^ 2 / C := (eq_div_iff hC).mpr hd
      _ = C⁻¹ * R z ^ 2 := div_eq_inv_mul _ _
  let : ConnectedSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} :=
    isConnected_iff_connectedSpace.mp (Intrinsic.PeriodDomain.Multiplicity.native_domain_connected E P hP)
  exact RootRatio.Frame.continuous_root_ratio_constant f R
    ((Quadratic.ballHolomorphic_continuous B.halfFrame hGeometry.2.2.2.2.1).comp
      (OneBallCoordinates.Multiplicity.nativeOneBallPoint_continuous E P hP hμ)) R.continuous
    (fun z => (hGeometry.2.2.2.2.2.1 _).1)
    (Intrinsic.FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he) C⁻¹ hsquare (Intrinsic.PeriodDomain.Multiplicity.nativeOrigin E P hP)

end Multiplicity

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneHalfFrame
