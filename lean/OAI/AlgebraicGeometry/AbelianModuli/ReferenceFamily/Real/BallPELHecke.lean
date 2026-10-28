import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPEL
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMarkingBallTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ComparisonMarkedLevel
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparisonAction

/-! # Ball PEL Hecke -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELHecke

noncomputable section

/-! Rational isometries of an original PEL fiber's Hermitian space
give actual paired quotients between its full-ball objects. The original
integral lattice supplies the denominator and every ordered level label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.CategoryTheory.MonObj

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

attribute [local irreducible] Intrinsic.BallCoordinateData.NativeBallCoordinateData.fiberAt
  Intrinsic.BallCoordinateData.NativeBallCoordinateData.pointTransport PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject.original_embedding_rank [IsGalois ℚ E]
    (A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ) (i : Fin s) :
    LieRanks.HasLieRank A.polarized.abelian A.action
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i) := by
  have hr := A.complexFiber_embedding_rank κ hκ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (Category.id_comp _) hP i
  exact LieTransport.hasLieRank_transport (A.action.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) A.action
    A.polarized.abelian.pullbackIdIso (PEL.Objects.PELIso.pullbackId A).action _ _ hr

namespace RealBallPELHecke

variable [NeZero N]
    (A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian PA
local notation "Λ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A.polarized.abelian PA A.action s hs rfl hdegree
local notation "eΛ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso.IntrinsicPELMarking.nativeIntegralMarking A.polarized.abelian PA A.action s hs rfl hdegree
local notation "m₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree
local notation "H" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati P.normalizedImaginaryScalar

def latticeLabel (l : Λ) : Multiplicative (Fin (2 * (3 * s)) → ZMod N) :=
  ChangedPELModel.RealChangedPEL.originalLevelLabel A ((eΛ).symm l)

theorem latticeLabel_surjective : Function.Surjective (latticeLabel A hs hdegree) := by
  intro c
  obtain ⟨l, hl⟩ := ChangedPELModel.RealChangedPEL.originalLevelLabel_surjective A c
  refine ⟨eΛ l, ?_⟩
  change ChangedPELModel.RealChangedPEL.originalLevelLabel A ((eΛ).symm (eΛ l)) = c
  rw [(eΛ).symm_apply_apply]
  exact hl

theorem latticeLabel_congruent (l m : Λ) (h : ∃ k : Λ, m - l = N • k) :
    latticeLabel A hs hdegree m = latticeLabel A hs hdegree l := by
  apply ChangedPELModel.RealChangedPEL.originalLevelLabel_congruent
  obtain ⟨k, hk⟩ := h
  refine ⟨(eΛ).symm k, ?_⟩
  simpa only [map_sub, map_nsmul] using congrArg (eΛ).symm hk

omit [NeZero N] in
theorem original_marking_inverse (l : Λ) :
    m₀ (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) ((eΛ).symm l)) = l.val := by
  change (eΛ ((eΛ).symm l)).val = l.val
  exact congrArg Subtype.val ((eΛ).apply_symm_apply l)

theorem original_level (l : Λ) :
    Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint A.polarized (latticeLabel A hs hdegree l) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A₀).toOver) ((N : ℝ)⁻¹ • ((m₀).symm l.val).val) := by
  have h := ChangedPELModel.RealChangedPEL.originalLevelLabel_point A ((eΛ).symm l)
  have hm : (m₀).symm l.val = LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) ((eΛ).symm l) := by
    apply (m₀).injective
    rw [(m₀).apply_symm_apply]
    exact (original_marking_inverse A hs hdegree l).symm
  change ((A.polarized.level.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
    (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (ChangedPELModel.RealChangedPEL.originalLevelLabel A ((eΛ).symm l)))).val ≫
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.polarized.abelian PA).inv = _
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg (fun v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ =>
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A₀).toOver) ((N : ℝ)⁻¹ • v.val)) hm.symm

variable (D : Intrinsic.BallCoordinateData.NativeBallCoordinateData A hs hdegree) (hP : P.IsAdmissible)

omit [NeZero N] in
theorem fiber_integral (z : P.Domain) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (D.fiberAt hP z).marking v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP z).model.model.abelian ↔ v ∈ Λ := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
  let c := Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.polarized.abelian PA A.action s hs rfl hdegree
  have hc := Marked.PeriodTransport.IntrinsicPELMarking.coordinates_mem_markedLattice A.polarized.abelian PA A.action s hs rfl hdegree (c.symm v)
  change c (c.symm v) ∈ Λ ↔ c.symm v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A₀ at hc
  rw [c.apply_symm_apply] at hc
  exact ((D.fiberAt hP z).marking_integral v).trans hc.symm

omit [NeZero N] in
theorem original_integral (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : (m₀).symm v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A₀ ↔ v ∈ Λ := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
  let c := Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.polarized.abelian PA A.action s hs rfl hdegree
  have hc := Marked.PeriodTransport.IntrinsicPELMarking.coordinates_mem_markedLattice A.polarized.abelian PA A.action s hs rfl hdegree (c.symm v)
  change c (c.symm v) ∈ Λ ↔ c.symm v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A₀ at hc
  rw [c.apply_symm_apply] at hc
  exact hc.symm

theorem fiber_level (z : P.Domain) (l : Λ) :
    Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint (D.fiberAt hP z).object.polarized (latticeLabel A hs hdegree l) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.fiberAt hP z).model.model.abelian.toOver)
        ((N : ℝ)⁻¹ • ((D.fiberAt hP z).marking l.val).val) := by
  have h := (D.fiberAt hP z).marking_level ((eΛ).symm l)
  rw [original_marking_inverse] at h
  apply Over.OverMorphism.ext
  change (show (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ (D.fiberAt hP z).object.polarized.abelian.scheme
    from ((D.fiberAt hP z).object.polarized.level.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (latticeLabel A hs hdegree l))).val).left ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact congrArg (fun p => p.left) h

omit [NeZero N] in
include hP in
theorem original_pairing_isometry (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian H x y) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.ChernPairing.nativePolarizationForm A.polarized ((m₀).symm (u v)) ((m₀).symm (u w)) =
      Intrinsic.ChernPairing.nativePolarizationForm A.polarized ((m₀).symm v) ((m₀).symm w) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.polarized.abelian PA A.action
  have ht (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) := Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_trace A.polarized A.action s hs rfl hdegree
    A.rosati P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 x y
  change Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A.polarized A.action s hs rfl hdegree (u v) (u w) =
    Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A.polarized A.action s hs rfl hdegree v w
  exact (ht (u v) (u w)).symm.trans
    ((congrArg (fun t : E => Algebra.trace ℚ E (P.normalizedImaginaryScalar * t)) (hu v w)).trans (ht v w))

theorem fiber_pairing_isometry (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian H x y) (v t : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP w).object.polarized
      ((D.fiberAt hP w).marking (u v)) ((D.fiberAt hP w).marking (u t)) =
    Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP z).object.polarized
      ((D.fiberAt hP z).marking v) ((D.fiberAt hP z).marking t) := by
  rw [(D.fiberAt hP w).marking_polarization (D.pointTransport hP w).property.1,
    (D.fiberAt hP z).marking_polarization (D.pointTransport hP z).property.1]
  exact original_pairing_isometry A hs hdegree hP u hu v t

attribute [local irreducible] Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods Intrinsic.ChernPairing.nativePolarizationForm Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport

def transport (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP z).model.model.abelian ≃ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP w).model.model.abelian :=
  Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport (D.fiberAt hP z).object.polarized (D.fiberAt hP z).object.action
    (D.fiberAt hP z).fieldMarking (D.fiberAt hP w).object.polarized (D.fiberAt hP w).object.action
    (D.fiberAt hP w).fieldMarking u

theorem transport_marking (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    transport A hs hdegree D hP z w u ((D.fiberAt hP z).marking v) = (D.fiberAt hP w).marking (u v) :=
  Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_marking _ _ _ _ _ _ u v

theorem transport_symm_marking (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (transport A hs hdegree D hP z w u).symm ((D.fiberAt hP w).marking v) =
      (D.fiberAt hP z).marking (u.symm v) :=
  Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_symm_marking _ _ _ _ _ _ u v

theorem transport_integral (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (n : ℕ)
    (m : Λ →ₗ[ℤ] Λ) (hm : ∀ l, (m l).val = n • u l.val)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP z).model.model.abelian)
    (hx : x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP z).model.model.abelian) :
    n • transport A hs hdegree D hP z w u x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP w).model.model.abelian := by
  let v := (D.fiberAt hP z).marking.symm x
  have hxv : (D.fiberAt hP z).marking v = x := (D.fiberAt hP z).marking.apply_symm_apply x
  have hv := (fiber_integral A hs hdegree D hP z v).mp (hxv.symm ▸ hx)
  have htarget := (fiber_integral A hs hdegree D hP w (n • u v)).mpr
    (hm ⟨v, hv⟩ ▸ (m ⟨v, hv⟩).property)
  have he : n • transport A hs hdegree D hP z w u x =
      (D.fiberAt hP w).marking (n • u v) := by
    calc
      _ = n • transport A hs hdegree D hP z w u ((D.fiberAt hP z).marking v) :=
        congrArg (fun t => n • transport A hs hdegree D hP z w u t) hxv.symm
      _ = n • (D.fiberAt hP w).marking (u v) :=
        congrArg (fun t => n • t) (transport_marking A hs hdegree D hP z w u v)
      _ = _ := (map_nsmul (D.fiberAt hP w).marking n (u v)).symm
  exact he.symm ▸ htarget

theorem transport_inverse_integral (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (n : ℕ)
    (m : Λ →ₗ[ℤ] Λ) (hm : ∀ l, (m l).val = n • u.symm l.val)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP w).model.model.abelian)
    (hx : x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP w).model.model.abelian) :
    n • (transport A hs hdegree D hP z w u).symm x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP z).model.model.abelian := by
  let v := (D.fiberAt hP w).marking.symm x
  have hxv : (D.fiberAt hP w).marking v = x := (D.fiberAt hP w).marking.apply_symm_apply x
  have hv := (fiber_integral A hs hdegree D hP w v).mp (hxv.symm ▸ hx)
  have htarget := (fiber_integral A hs hdegree D hP z (n • u.symm v)).mpr
    (hm ⟨v, hv⟩ ▸ (m ⟨v, hv⟩).property)
  have he : n • (transport A hs hdegree D hP z w u).symm x =
      (D.fiberAt hP z).marking (n • u.symm v) := by
    calc
      _ = n • (transport A hs hdegree D hP z w u).symm ((D.fiberAt hP w).marking v) :=
        congrArg (fun t => n • (transport A hs hdegree D hP z w u).symm t) hxv.symm
      _ = n • (D.fiberAt hP z).marking (u.symm v) :=
        congrArg (fun t => n • t) (transport_symm_marking A hs hdegree D hP z w u v)
      _ = _ := (map_nsmul (D.fiberAt hP z).marking n (u.symm v)).symm
  exact he.symm ▸ htarget

omit [NeZero N] in
theorem lineActionVia_span (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian H x y) (z w : P.Domain)
    (hw : w.val = P.lineActionVia D.normalizer u z.val) :
    (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val}).map
      (NegativeLine.normalizedLineMap D.normalizer D.normalizer (EmbeddedLinearGroup.embeddedLinearIso u (P.embeddings P.distinguished))).toLinearMap =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w.val} := by
  have he (x y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
      Complex.HermitianMatrixForm.complexHermitianMatrixForm ((H).map (P.embeddings P.distinguished)) (D.normalizer x) (D.normalizer y) =
        Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) x y :=
    (Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply _ _ _).trans
      ((D.hermitian x y).trans (Normalized.HodgeLine.complexMatrixHermitian_diagonal P.μ P.b x y))
  have hl := Normalized.HermitianTransport.normalizedEmbeddedIsometry_last_ne_zero H H u hu (P.embeddings P.distinguished)
    (P.μ P.b) D.normalizer D.normalizer he he z.val
      ((Datum.RankThreePELDatum.mem_domain_iff_diagonal z.val).mp z.property)
  rw [hw]
  exact NegativeLine.map_lineVector_span
    (NegativeLine.normalizedLineMap D.normalizer D.normalizer (EmbeddedLinearGroup.embeddedLinearIso u (P.embeddings P.distinguished))).toLinearMap
    z.val hl

theorem transport_hodge [IsGalois ℚ E] (hκ : κ.comp iota = P.μ)
    (z w : P.Domain) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian H x y)
    (hw : w.val = P.lineActionVia D.normalizer u z.val) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (D.fiberAt hP z).model.model.abelian)
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (D.fiberAt hP w).model.model.abelian)
      (transport A hs hdegree D hP z w u).toLinearMap := by
  apply Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_isHodgeMap_of_line_transport
    (D.fiberAt hP z).object.polarized (D.fiberAt hP z).object.action (D.fiberAt hP z).fieldMarking
    (D.fiberAt hP w).object.polarized (D.fiberAt hP w).object.action (D.fiberAt hP w).fieldMarking
    u s hs rfl hdegree P hP (D.fiberAt hP z).object.rosati (D.fiberAt hP w).object.rosati
    (fiber_pairing_isometry A hs hdegree D hP z w u hu) D.normalizer z.val w.val
    (D.fiberAt_kernel hP z) (D.fiberAt_kernel hP w)
    (lineActionVia_span A hs hdegree D u hu z w hw)
  · exact (D.fiberAt hP z).object.original_embedding_rank hP hκ
  · exact (D.fiberAt hP w).object.original_embedding_rank hP hκ

end RealBallPELHecke

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELHecke
