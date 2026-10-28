import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELHecke
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledPeriodPELQuotients

/-! # Ball PEL Hecke Quotients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELHeckeQuotients.RealBallPELHecke

noncomputable section

/-! A cleared rational isometry gives actual paired PEL quotients
between the full-ball objects, with their original ordered level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

attribute [local irreducible] Intrinsic.BallCoordinateData.NativeBallCoordinateData.fiberAt
  Intrinsic.BallCoordinateData.NativeBallCoordinateData.pointTransport PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap
  Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport Intrinsic.ChernPairing.nativePolarizationForm Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods

attribute [local implicit_reducible] Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.object ChangedPELModel.RealChangedPEL.object
  Picard.ThetaConstruction.PrimitiveDual.Geometric.PrimitiveDualConstruction.polarized Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.abelianScheme
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.toOver

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s}
    {iota : E →+* K} {κ : K →+* ℂ}
    (A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (D : Intrinsic.BallCoordinateData.NativeBallCoordinateData A hs hdegree) (hP : P.IsAdmissible)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
local notation "Λ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A.polarized.abelian PA A.action s hs rfl hdegree
local notation "H" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati P.normalizedImaginaryScalar

private theorem fiber_native_integral_iff (t : P.Domain)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP t).model.model.abelian) :
    x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP t).object.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP t).object.polarized)) ↔
        x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP t).model.model.abelian := by
  unfold Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods
  rfl

private theorem transport_native_hodge [IsGalois ℚ E] (hκ : κ.comp iota = P.μ)
    (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian H x y)
    (hw : w.val = P.lineActionVia D.normalizer u z.val) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP z).object.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP z).object.polarized)))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP w).object.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP w).object.polarized)))
      (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u).toLinearMap := by
  exact BallPELHecke.RealBallPELHecke.transport_hodge A hs hdegree D hP hκ z w u hu hw

private theorem transport_native_polarization
    (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian H x y)
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP z).model.model.abelian) :
    Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP w).object.polarized
        (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u x) (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u y) =
      Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP z).object.polarized x y :=
  Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_polarization
    (D.fiberAt hP z).object.polarized (D.fiberAt hP z).object.action (D.fiberAt hP z).fieldMarking
    (D.fiberAt hP w).object.polarized (D.fiberAt hP w).object.action (D.fiberAt hP w).fieldMarking u
    (BallPELHecke.RealBallPELHecke.fiber_pairing_isometry A hs hdegree D hP z w u hu) x y

private theorem transport_native_level
    (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (n : ℕ) (m : Λ →ₗ[ℤ] Λ)
    (hm : ∀ l, (m l).val = n • u l.val)
    (hcongr : ∀ l : Λ, ∃ k : Λ, m l - l = N • k) (l : Λ) :
    Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint (D.fiberAt hP w).object.polarized
      (BallPELHecke.RealBallPELHecke.latticeLabel A hs hdegree l) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.fiberAt hP w).model.model.abelian.toOver)
        ((N : ℝ)⁻¹ • (n • BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u
          ((D.fiberAt hP z).marking l.val)).val) := by
  have heq : (D.fiberAt hP w).marking (m l).val =
      n • BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u ((D.fiberAt hP z).marking l.val) := by
    calc
      _ = (D.fiberAt hP w).marking (n • u l.val) :=
        congrArg (D.fiberAt hP w).marking (hm l)
      _ = n • (D.fiberAt hP w).marking (u l.val) :=
        map_nsmul (D.fiberAt hP w).marking n (u l.val)
      _ = _ := congrArg (fun v => n • v)
        (BallPELHecke.RealBallPELHecke.transport_marking A hs hdegree D hP z w u l.val).symm
  exact (congrArg (Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint (D.fiberAt hP w).object.polarized)
    (BallPELHecke.RealBallPELHecke.latticeLabel_congruent A hs hdegree l (m l) (hcongr l))).symm.trans
      ((BallPELHecke.RealBallPELHecke.fiber_level A hs hdegree D hP w (m l)).trans
        (congrArg (fun v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP w).model.model.abelian =>
          HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.fiberAt hP w).model.model.abelian.toOver)
            ((N : ℝ)⁻¹ • v.val)) heq))

private theorem transport_native_action
    (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (a : NumberField.RingOfIntegers E) :
    (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u).toLinearMap.comp
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift
        (A := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP z).object.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP z).object.polarized))
        (B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP z).object.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP z).object.polarized))
        (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap (D.fiberAt hP z).object.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP z).object.polarized)
          (D.fiberAt hP z).object.action a)) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift
        (A := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP w).object.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP w).object.polarized))
        (B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP w).object.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP w).object.polarized))
        (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap (D.fiberAt hP w).object.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP w).object.polarized)
          (D.fiberAt hP w).object.action a)).comp
            (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u).toLinearMap := by
  unfold BallPELHecke.RealBallPELHecke.transport
  apply LinearMap.ext
  intro x
  have h := Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_action
    (E := E) (g := 3 * s) (N := N) (δ := P.polarizationType)
    (D.fiberAt hP z).object.polarized (D.fiberAt hP z).object.action (D.fiberAt hP z).fieldMarking
    (D.fiberAt hP w).object.polarized (D.fiberAt hP w).object.action (D.fiberAt hP w).fieldMarking u a
  exact LinearMap.congr_fun h x

private theorem transport_native_integral
    (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (n : ℕ) (m : Λ →ₗ[ℤ] Λ) (hm : ∀ l, (m l).val = n • u l.val)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP z).model.model.abelian)
    (hx : x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP z).object.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP z).object.polarized))) :
    n • (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u) x ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP w).object.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP w).object.polarized)) := by
  exact (fiber_native_integral_iff A hs hdegree D hP w _).mpr
    (BallPELHecke.RealBallPELHecke.transport_integral A hs hdegree D hP z w u n m hm x
      ((fiber_native_integral_iff A hs hdegree D hP z x).mp hx))

private theorem transport_inverse_native_integral
    (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (n : ℕ) (m : Λ →ₗ[ℤ] Λ) (hm : ∀ l, (m l).val = n • u.symm l.val)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP w).model.model.abelian)
    (hx : x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP w).object.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP w).object.polarized))) :
    n • (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u).symm x ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP z).object.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP z).object.polarized)) := by
  exact (fiber_native_integral_iff A hs hdegree D hP z _).mpr
    (BallPELHecke.RealBallPELHecke.transport_inverse_integral A hs hdegree D hP z w u n m hm x
      ((fiber_native_integral_iff A hs hdegree D hP w x).mp hx))

attribute [local irreducible] BallPELHecke.RealBallPELHecke.transport

theorem exists_paired_quotient [IsGalois ℚ E] [CharZero K] (hκ : κ.comp iota = P.μ)
    (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian H x y)
    (hw : w.val = P.lineActionVia D.normalizer u z.val)
    (n : ℕ) (hn : 0 < n) (hmod : Nat.ModEq N (n ^ 2) 1)
    (m m' : Λ →ₗ[ℤ] Λ)
    (hm : ∀ l, (m l).val = n • u l.val) (hm' : ∀ l, (m' l).val = n • u.symm l.val)
    (hcongr : ∀ l : Λ, ∃ k : Λ, m l - l = N • k) :
    Nonempty (Paired.PELQuotients.PairedPELQuotient (D.fiberAt hP z).object (D.fiberAt hP w).object (n ^ 2)) := by
  apply Exists.nonempty
  refine ScaledPeriodPELQuotients.exists_paired_quotient_of_scaled_period_isometry
    (E := E) (K := K) (P := P) (iota := iota) (N := N)
    (t := Spec.map (CommRingCat.ofHom κ)) (I := Λ)
    (D.fiberAt hP z).object (D.fiberAt hP w).object (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u)
    ?_ ?_ ?_ n hn hmod ?_ ?_
    (BallPELHecke.RealBallPELHecke.latticeLabel A hs hdegree) (BallPELHecke.RealBallPELHecke.latticeLabel_surjective A hs hdegree)
    (fun l => (D.fiberAt hP z).marking l.val) ?_ ?_
  · exact transport_native_hodge A hs hdegree D hP hκ z w u hu hw
  · exact transport_native_polarization A hs hdegree D hP z w u hu
  · exact transport_native_action A hs hdegree D hP z w u
  · exact transport_native_integral A hs hdegree D hP z w u n m hm
  · exact transport_inverse_native_integral A hs hdegree D hP z w u n m' hm'
  · exact BallPELHecke.RealBallPELHecke.fiber_level A hs hdegree D hP z
  · have h := transport_native_level A hs hdegree D hP z w u n m hm hcongr
    exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELHeckeQuotients.RealBallPELHecke
