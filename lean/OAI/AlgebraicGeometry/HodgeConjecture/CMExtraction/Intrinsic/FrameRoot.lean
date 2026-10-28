import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain

/-! # Frame Root -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FrameRoot.Multiplicity

noncomputable section

/-! A global continuous square root of the determinant of the actual
native lower frame. The logarithm is normalized at the native origin. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

omit [IsGalois ℚ E] in
theorem native_domain_contractible (hP : P.IsAdmissible) :
    ContractibleSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} := by
  rw [PeriodDomain.Multiplicity.native_domain_eq_ball]
  apply (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_starConvex (P.μ P.b)).contractibleSpace
  exact (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_pathConnected (P.μ P.b) hP.2.2.2.1).nonempty

omit [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E] in
theorem native_domain_locallyPathConnected :
    LocallyPathConnectedSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} := by
  rw [PeriodDomain.Multiplicity.native_domain_eq_ball]
  exact (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b)).isOpen.locallyPathConnectedSpace

variable (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

def nativeLowerDet : C({z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}, ℂ) where
  toFun z := (Multiplicity.Period.nativeLowerFrame E P hP v e z).det
  continuous_toFun := by
    have hd : DifferentiableOn ℂ
        (fun z : Geometry.ComplexBall.PrescribedSignsB.BallChart => (Multiplicity.Period.nativeLowerFrame E P hP v e z).det) P.domain := by
      apply PeriodMatrixFamilies.Multiplicity.matrix_family_det_differentiable
      apply PeriodFrameFamilies.Multiplicity.lowerFrame_differentiable
      intro z _
      rw [Multiplicity.Period.native_frame_denominator E P z]
      exact (map_ne_zero _).mpr hP.2.2.1
    exact continuousOn_iff_continuous_domRestrict.mp hd.continuousOn

include hμ hv he

theorem nativeLowerDet_ne_zero (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    nativeLowerDet E P hP v e z ≠ 0 :=
  PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he z z.property

theorem existsUnique_nativeLowerDetLog :
    ∃! L : C({z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}, ℂ),
      L (PeriodDomain.Multiplicity.nativeOrigin E P hP) = Complex.log (nativeLowerDet E P hP v e (PeriodDomain.Multiplicity.nativeOrigin E P hP)) ∧
      ∀ z, Complex.exp (L z) = nativeLowerDet E P hP v e z := by
  let : ContractibleSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} := native_domain_contractible E P hP
  let : LocallyPathConnectedSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} :=
    native_domain_locallyPathConnected E P
  obtain ⟨L, ⟨hbase, hL⟩, huniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts (nativeLowerDet E P hP v e)
      (Complex.exp_log (nativeLowerDet_ne_zero E P hP hμ v hv e he (PeriodDomain.Multiplicity.nativeOrigin E P hP)))
      (fun z => by simpa using nativeLowerDet_ne_zero E P hP hμ v hv e he z)
  refine ⟨L, ⟨hbase, fun z => congrFun hL z⟩, fun M hM => ?_⟩
  exact huniq M ⟨hM.1, funext hM.2⟩

def nativeLowerDetLog : C({z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}, ℂ) :=
  (existsUnique_nativeLowerDetLog E P hP hμ v hv e he).choose

theorem exp_nativeLowerDetLog (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    Complex.exp (nativeLowerDetLog E P hP hμ v hv e he z) = nativeLowerDet E P hP v e z :=
  (existsUnique_nativeLowerDetLog E P hP hμ v hv e he).choose_spec.1.2 z

def nativeFrameRoot : C({z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}, ℂ) :=
  ⟨fun z => Complex.exp (nativeLowerDetLog E P hP hμ v hv e he z / 2), by fun_prop⟩

theorem nativeFrameRoot_sq (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    nativeFrameRoot E P hP hμ v hv e he z ^ 2 = (Multiplicity.Period.nativeLowerFrame E P hP v e z).det := by
  change Complex.exp (_ / 2) ^ 2 = _
  rw [← Complex.exp_nat_mul]
  convert exp_nativeLowerDetLog E P hP hμ v hv e he z using 1
  congr 1
  ring
  rfl

theorem nativeFrameRoot_ne_zero (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    nativeFrameRoot E P hP hμ v hv e he z ≠ 0 := Complex.exp_ne_zero _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FrameRoot.Multiplicity
