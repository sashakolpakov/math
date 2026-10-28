import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELHecke
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.IsoCoordinates
import OAI.RepresentationTheory.Theta.Geometric.MarkedPolarizationIsometry
import OAI.RepresentationTheory.Theta.Geometric.LatticeDeterminantCongruence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryDeterminant
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence

/-! # Ball PEL Orbits -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELOrbits.RealBallPELOrbits

noncomputable section

/-! The fibers of the full-ball PEL construction are exactly the orbits
of the prescribed principal subgroup on the original integral lattice.
Both directions retain the original polarization and ordered level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.CategoryTheory.MonObj

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

attribute [local irreducible] Intrinsic.BallCoordinateData.NativeBallCoordinateData.fiberAt
  Intrinsic.BallCoordinateData.NativeBallCoordinateData.pointTransport PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap
  Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods Intrinsic.ChernPairing.nativePolarizationForm Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport

attribute [local implicit_reducible] Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.object ChangedPELModel.RealChangedPEL.object
  Picard.ThetaConstruction.PrimitiveDual.Geometric.PrimitiveDualConstruction.polarized Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.abelianScheme
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.toOver

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s}
    {iota : E →+* K} {κ : K →+* ℂ}
    (A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (D : Intrinsic.BallCoordinateData.NativeBallCoordinateData A hs hdegree) (hP : P.IsAdmissible)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian PA
local notation "Λ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A.polarized.abelian PA A.action s hs rfl hdegree
local notation "m₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree
local notation "H" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati P.normalizedImaginaryScalar
local notation "Γ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup (R := E) (Submodule.toAddSubgroup Λ) N ⊓
  Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)

variable (z w : P.Domain) (α : PEL.Objects.PELIso (D.fiberAt hP z).object (D.fiberAt hP w).object)

theorem fiber_native_integral (t : P.Domain)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP t).model.model.abelian) :
    x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP t).object.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP t).object.polarized)) ↔
        x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP t).model.model.abelian := by
  unfold Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods
  rfl

theorem fiber_field_integral (t : P.Domain) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (D.fiberAt hP t).fieldMarking v ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP t).object.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP t).object.polarized)) ↔ v ∈ Λ :=
  (fiber_native_integral A hs hdegree D hP t _).trans (BallPELHecke.RealBallPELHecke.fiber_integral A hs hdegree D hP t v)

def coordinateChange : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  Marked.IsoCoordinates.NativeFieldMarking.isoCoordinates (D.fiberAt hP z).object.polarized
    (D.fiberAt hP w).object.polarized (D.fiberAt hP z).object.action
    (D.fiberAt hP w).object.action α.polarized α.action
    (D.fiberAt hP z).fieldMarking (D.fiberAt hP w).fieldMarking

theorem coordinateChange_integral (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    v ∈ Λ ↔ coordinateChange A hs hdegree D hP z w α v ∈ Λ :=
  Marked.IsoCoordinates.NativeFieldMarking.isoCoordinates_integral _ _ _ _ α.polarized α.action
    (D.fiberAt hP z).fieldMarking (D.fiberAt hP w).fieldMarking Λ
    (fiber_field_integral A hs hdegree D hP z) (fiber_field_integral A hs hdegree D hP w) v

theorem coordinateChange_congruence (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hv : v ∈ Λ) :
    ∃ y ∈ Λ, coordinateChange A hs hdegree D hP z w α v - v = N • y :=
  Marked.IsoCoordinates.NativeFieldMarking.isoCoordinates_congruence _ _ _ _ α.polarized α.action
    (D.fiberAt hP z).fieldMarking (D.fiberAt hP w).fieldMarking Λ
    (fiber_field_integral A hs hdegree D hP w) (BallPELHecke.RealBallPELHecke.latticeLabel A hs hdegree)
    (BallPELHecke.RealBallPELHecke.fiber_level A hs hdegree D hP z) (BallPELHecke.RealBallPELHecke.fiber_level A hs hdegree D hP w) v hv

theorem coordinateChange_polarization (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.ChernPairing.nativePolarizationForm A.polarized
      ((m₀).symm (coordinateChange A hs hdegree D hP z w α x))
      ((m₀).symm (coordinateChange A hs hdegree D hP z w α y)) =
      Intrinsic.ChernPairing.nativePolarizationForm A.polarized ((m₀).symm x) ((m₀).symm y) := by
  exact Marked.IsoCoordinates.NativeFieldMarking.isoCoordinates_polarization
    (D.fiberAt hP z).object.polarized (D.fiberAt hP w).object.polarized
    (D.fiberAt hP z).object.action (D.fiberAt hP w).object.action α.polarized α.action
    (D.fiberAt hP z).fieldMarking (D.fiberAt hP w).fieldMarking
    (fun x y => Intrinsic.ChernPairing.nativePolarizationForm A.polarized ((m₀).symm x) ((m₀).symm y))
    ((D.fiberAt hP z).marking_polarization (D.pointTransport hP z).property.1)
    ((D.fiberAt hP w).marking_polarization (D.pointTransport hP w).property.1) x y

theorem coordinateChange_unitary (v t : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Datum.RankThreePELDatum.matrixHermitian H (coordinateChange A hs hdegree D hP z w α v)
      (coordinateChange A hs hdegree D hP z w α t) = Datum.RankThreePELDatum.matrixHermitian H v t := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.polarized.abelian PA A.action
  apply RepresentationTheory.Theta.Geometric.MarkedPolarizationIsometry.markedPolarization_isometry_hermitian A.polarized A.polarized A.action A.action
    s hs rfl hdegree A.rosati A.rosati P.normalizedImaginaryScalar
    (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1
    (coordinateChange A hs hdegree D hP z w α)
  intro x y
  exact coordinateChange_polarization A hs hdegree D hP z w α x y

theorem coordinateChange_determinant (hN : 3 ≤ N) :
    LinearMap.det (coordinateChange A hs hdegree D hP z w α).toLinearMap = 1 := by
  let b := (Intrinsic.Torsion.IntrinsicTorsion.periodBasis A₀).map
    (Intrinsic.MarkedLatticeIso.IntrinsicPELMarking.nativeIntegralMarking A.polarized.abelian PA A.action s hs rfl hdegree)
  obtain ⟨a, ha, he⟩ := RepresentationTheory.Theta.Geometric.LatticeDeterminantCongruence.lattice_determinant_congruence Λ b
    (Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice_full_stable A.polarized.abelian PA A.action s hs rfl hdegree).2.1
    (coordinateChange A hs hdegree D hP z w α) N (NeZero.ne N)
    (coordinateChange_congruence A hs hdegree D hP z w α)
  apply DeterminantCongruence.norm_one_integral_congruence_eq_one _ a ha N hN he
  exact Hermitian.IsometryDeterminant.TraceReconstruction.matrixPairing_isometry_det_norm_one H
    (Intrinsic.HermitianNondegenerate.IntrinsicHermitianMarking.markedHermitianMatrix_det_ne_zero A.polarized A.action s hs rfl hdegree A.rosati
      P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1)
    (coordinateChange A hs hdegree D hP z w α) (coordinateChange_unitary A hs hdegree D hP z w α)

theorem coordinateChange_mem (hN : 3 ≤ N) : coordinateChange A hs hdegree D hP z w α ∈ Γ := by
  refine ⟨⟨coordinateChange_integral A hs hdegree D hP z w α,
    coordinateChange_congruence A hs hdegree D hP z w α⟩,
    coordinateChange_unitary A hs hdegree D hP z w α, ?_⟩
  change LinearEquiv.det (coordinateChange A hs hdegree D hP z w α) = 1
  apply Units.ext
  simp only [LinearEquiv.coe_det, Units.val_one]
  exact coordinateChange_determinant A hs hdegree D hP z w α hN

theorem coordinateChange_line :
    w.val = P.lineActionVia D.normalizer (coordinateChange A hs hdegree D hP z w α) z.val := by
  exact Marked.IsoCoordinates.NativeFieldMarking.isoCoordinates_line_action _ _ _ _ α.polarized α.action
    (D.fiberAt hP z).fieldMarking (D.fiberAt hP w).fieldMarking
    (P.embeddings P.distinguished) D.normalizer z.val w.val
    (D.fiberAt_kernel hP z) (D.fiberAt_kernel hP w)

theorem exists_principal_of_iso (hN : 3 ≤ N)
    (h : Nonempty (PEL.Objects.PELIso (D.fiberAt hP z).object (D.fiberAt hP w).object)) :
    ∃ u ∈ Γ, w.val = P.lineActionVia D.normalizer u z.val := by
  obtain ⟨α⟩ := h
  exact ⟨coordinateChange A hs hdegree D hP z w α,
    coordinateChange_mem A hs hdegree D hP z w α hN,
    coordinateChange_line A hs hdegree D hP z w α⟩

theorem principal_transport_integral (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hu : u ∈ Γ)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP z).model.model.abelian) :
    x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP z).model.model.abelian ↔
      BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u x ∈
        Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP w).model.model.abelian := by
  let v := (D.fiberAt hP z).marking.symm x
  have hx : (D.fiberAt hP z).marking v = x := (D.fiberAt hP z).marking.apply_symm_apply x
  have he : BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u x =
      (D.fiberAt hP w).marking (u v) :=
    (congrArg (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u) hx).symm.trans
      (BallPELHecke.RealBallPELHecke.transport_marking A hs hdegree D hP z w u v)
  have hA := BallPELHecke.RealBallPELHecke.fiber_integral A hs hdegree D hP z v
  have hB := BallPELHecke.RealBallPELHecke.fiber_integral A hs hdegree D hP w (u v)
  rw [hx] at hA
  rw [← he] at hB
  exact hA.trans ((hu.1.1 v).trans hB.symm)

theorem principal_transport_polarization (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hu : u ∈ Γ)
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP z).model.model.abelian) :
    Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP w).object.polarized
      (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u x)
      (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u y) =
        Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP z).object.polarized x y := by
  let v := (D.fiberAt hP z).marking.symm x
  let t := (D.fiberAt hP z).marking.symm y
  have hx : (D.fiberAt hP z).marking v = x := (D.fiberAt hP z).marking.apply_symm_apply x
  have hy : (D.fiberAt hP z).marking t = y := (D.fiberAt hP z).marking.apply_symm_apply y
  have he : BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u x =
      (D.fiberAt hP w).marking (u v) :=
    (congrArg (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u) hx).symm.trans
      (BallPELHecke.RealBallPELHecke.transport_marking A hs hdegree D hP z w u v)
  have he' : BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u y =
      (D.fiberAt hP w).marking (u t) :=
    (congrArg (BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u) hy).symm.trans
      (BallPELHecke.RealBallPELHecke.transport_marking A hs hdegree D hP z w u t)
  calc
    _ = Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP w).object.polarized
        ((D.fiberAt hP w).marking (u v)) ((D.fiberAt hP w).marking (u t)) :=
      congrArg₂ (fun a b => Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP w).object.polarized a b) he he'
    _ = Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP z).object.polarized
        ((D.fiberAt hP z).marking v) ((D.fiberAt hP z).marking t) :=
      BallPELHecke.RealBallPELHecke.fiber_pairing_isometry A hs hdegree D hP z w u hu.2.1 v t
    _ = _ := congrArg₂ (fun a b => Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP z).object.polarized a b) hx hy

variable [IsGalois ℚ E] (hκ : κ.comp iota = P.μ)

def principalComparison (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hu : u ∈ Γ)
    (hw : w.val = P.lineActionVia D.normalizer u z.val) :
    RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison.NativePolarizedComparison (D.fiberAt hP z).object.polarized (D.fiberAt hP w).object.polarized where
  periods := BallPELHecke.RealBallPELHecke.transport A hs hdegree D hP z w u
  hodge := BallPELHecke.RealBallPELHecke.transport_hodge A hs hdegree D hP hκ z w u hu.2.1 hw
  integral x := (fiber_native_integral A hs hdegree D hP z x).trans
    ((principal_transport_integral A hs hdegree D hP z w u hu x).trans
      (fiber_native_integral A hs hdegree D hP w _).symm)
  polarization := principal_transport_polarization A hs hdegree D hP z w u hu

omit [IsGalois ℚ E] in
theorem principal_level (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hu : u ∈ Γ) (l : Λ) :
    Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint (D.fiberAt hP w).object.polarized (BallPELHecke.RealBallPELHecke.latticeLabel A hs hdegree l) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.fiberAt hP w).model.model.abelian.toOver)
        ((N : ℝ)⁻¹ • ((D.fiberAt hP w).marking (u l.val)).val) := by
  let m : Λ := ⟨u l.val, (hu.1.1 l.val).mp l.property⟩
  have hm : ∃ k : Λ, m - l = N • k := by
    obtain ⟨k, hk, he⟩ := hu.1.2 l.val l.property
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩
  rw [← BallPELHecke.RealBallPELHecke.latticeLabel_congruent A hs hdegree l m hm]
  exact BallPELHecke.RealBallPELHecke.fiber_level A hs hdegree D hP w m

def principalIso (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hu : u ∈ Γ)
    (hw : w.val = P.lineActionVia D.normalizer u z.val) :
    PEL.Objects.PELIso (D.fiberAt hP z).object (D.fiberAt hP w).object where
  polarized := (principalComparison A hs hdegree D hP z w hκ u hu hw).toLevelIso
    (Polarized.ComparisonMarkedLevel.polarizedComparison_level_of_rational_labels (principalComparison A hs hdegree D hP z w hκ u hu hw)
      (BallPELHecke.RealBallPELHecke.latticeLabel A hs hdegree) (BallPELHecke.RealBallPELHecke.latticeLabel_surjective A hs hdegree)
      (fun l => (D.fiberAt hP z).marking l.val) (fun l => (D.fiberAt hP w).marking (u l.val))
      (N : ℝ)⁻¹ (BallPELHecke.RealBallPELHecke.fiber_level A hs hdegree D hP z) (principal_level A hs hdegree D hP w u hu)
      (fun l => BallPELHecke.RealBallPELHecke.transport_marking A hs hdegree D hP z w u l.val))
  action a := by
    apply (principalComparison A hs hdegree D hP z w hκ u hu hw).algebraicIso_action
      (D.fiberAt hP z).object.action (D.fiberAt hP w).object.action
    intro b x
    exact LinearMap.congr_fun (Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_action
      (D.fiberAt hP z).object.polarized (D.fiberAt hP z).object.action (D.fiberAt hP z).fieldMarking
      (D.fiberAt hP w).object.polarized (D.fiberAt hP w).object.action (D.fiberAt hP w).fieldMarking u b) x

include hκ in
theorem iso_iff_principal_orbit (hN : 3 ≤ N) :
    Nonempty (PEL.Objects.PELIso (D.fiberAt hP z).object (D.fiberAt hP w).object) ↔
      ∃ u ∈ Γ, w.val = P.lineActionVia D.normalizer u z.val := by
  constructor
  · exact exists_principal_of_iso A hs hdegree D hP z w hN
  · rintro ⟨u, hu, hw⟩
    exact ⟨principalIso A hs hdegree D hP z w hκ u hu hw⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELOrbits.RealBallPELOrbits
