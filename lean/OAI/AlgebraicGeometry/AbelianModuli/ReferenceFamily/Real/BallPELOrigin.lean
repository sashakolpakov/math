import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELHecke

/-! # Ball PEL Origin -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELOrigin.RealBallPELHecke

noncomputable section

/-! The center of the full-ball family is isomorphic to the original
PEL object, with its integral action, polarization, and ordered level. -/

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

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s}
    {iota : E →+* K} {κ : K →+* ℂ}
    (A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (D : Intrinsic.BallCoordinateData.NativeBallCoordinateData A hs hdegree) (hP : P.IsAdmissible)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian PA
local notation "m₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree

def originalFieldMarking :
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
  exact (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.polarized.abelian PA A.action s hs rfl hdegree).symm

def originPeriodMap :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (D.fiberAt hP D.point).model.model.abelian :=
  Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport A.polarized A.action (originalFieldMarking A hs hdegree)
    (D.fiberAt hP D.point).object.polarized (D.fiberAt hP D.point).object.action
    (D.fiberAt hP D.point).fieldMarking (LinearEquiv.refl E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))

theorem originPeriodMap_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    originPeriodMap A hs hdegree D hP ((m₀).symm v) = (D.fiberAt hP D.point).marking v :=
  Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_marking A.polarized A.action (originalFieldMarking A hs hdegree)
    (D.fiberAt hP D.point).object.polarized (D.fiberAt hP D.point).object.action
    (D.fiberAt hP D.point).fieldMarking (LinearEquiv.refl E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) v

theorem originPeriodMap_isHodgeMap [IsGalois ℚ E] (hκ : κ.comp iota = P.μ) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A₀)
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (D.fiberAt hP D.point).model.model.abelian)
      (originPeriodMap A hs hdegree D hP).toLinearMap := by
  let F := D.fiberAt hP D.point
  let mA := originalFieldMarking A hs hdegree
  have hz (v : Geometry.ComplexBall.PrescribedSignsB.Vec) : (Intrinsic.FieldMarkingTransport.IntrinsicFieldMarking.rationalMarking A.polarized A.action mA).toLinearMap.baseChange ℂ
      (PeriodEmbeddingChanges.fixedFirstComplexInclusion E (P.embeddings P.distinguished) D.normalizer v) ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A₀).ker ↔ v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector D.point.val} := by
    change (m₀).symm.toLinearMap.baseChange ℂ
      (PeriodEmbeddingChanges.fixedFirstComplexInclusion E (P.embeddings P.distinguished) D.normalizer v) ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A₀).ker ↔ _
    rw [PeriodEmbeddingChanges.fixedFirstComplexInclusion_native]
    exact (PEL.RealPeriodChanges.IntrinsicPELRealChanges.normalizedEmbeddingInclusion_kernel A.polarized A.action
      s hs rfl hdegree (P.embeddings P.distinguished) D.normalizer v).trans (by rw [D.hodgeLine])
  have hi : NegativeLine.normalizedLineMap D.normalizer D.normalizer
      (EmbeddedLinearGroup.embeddedLinearIso (LinearEquiv.refl E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (P.embeddings P.distinguished)) =
        LinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.Vec := by
    apply LinearEquiv.ext
    intro v
    change D.normalizer.symm (EmbeddedLinearGroup.embeddedLinearIso (LinearEquiv.refl E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
      (P.embeddings P.distinguished) (D.normalizer v)) = v
    rw [RepresentationTheory.Theta.Geometric.EmbeddedTransportComposition.embeddedLinearIso_refl_apply, D.normalizer.symm_apply_apply]
  apply Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_isHodgeMap_of_line_transport A.polarized A.action mA
    F.object.polarized F.object.action F.fieldMarking (LinearEquiv.refl E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    s hs rfl hdegree P hP A.rosati F.object.rosati
    (F.marking_polarization (D.pointTransport hP D.point).property.1)
    D.normalizer D.point.val D.point.val hz (D.fiberAt_kernel hP D.point) ?_
    (A.original_embedding_rank hP hκ) (F.object.original_embedding_rank hP hκ)
  rw [hi]
  exact Submodule.map_id _

theorem originPeriodMap_integral (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀) :
    x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A₀ ↔ originPeriodMap A hs hdegree D hP x ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP D.point).model.model.abelian := by
  let F := D.fiberAt hP D.point
  let v := m₀ x
  have hxv : (m₀).symm v = x := (m₀).symm_apply_apply x
  have he : originPeriodMap A hs hdegree D hP x = F.marking v :=
    (congrArg (originPeriodMap A hs hdegree D hP) hxv).symm.trans
      (originPeriodMap_marking A hs hdegree D hP v)
  have hA := BallPELHecke.RealBallPELHecke.original_integral A hs hdegree v
  have hB := BallPELHecke.RealBallPELHecke.fiber_integral A hs hdegree D hP D.point v
  rw [hxv] at hA
  rw [← he] at hB
  exact hA.trans hB.symm

theorem originPeriodMap_polarization (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀) :
    Intrinsic.ChernPairing.nativePolarizationForm (D.fiberAt hP D.point).object.polarized
      (originPeriodMap A hs hdegree D hP x) (originPeriodMap A hs hdegree D hP y) =
        Intrinsic.ChernPairing.nativePolarizationForm A.polarized x y := by
  let F := D.fiberAt hP D.point
  let v := m₀ x
  let w := m₀ y
  have hxv : (m₀).symm v = x := (m₀).symm_apply_apply x
  have hyw : (m₀).symm w = y := (m₀).symm_apply_apply y
  have he : originPeriodMap A hs hdegree D hP x = F.marking v :=
    (congrArg (originPeriodMap A hs hdegree D hP) hxv).symm.trans
      (originPeriodMap_marking A hs hdegree D hP v)
  have he' : originPeriodMap A hs hdegree D hP y = F.marking w :=
    (congrArg (originPeriodMap A hs hdegree D hP) hyw).symm.trans
      (originPeriodMap_marking A hs hdegree D hP w)
  calc
    _ = Intrinsic.ChernPairing.nativePolarizationForm F.object.polarized (F.marking v) (F.marking w) :=
      congrArg₂ (fun a b => Intrinsic.ChernPairing.nativePolarizationForm F.object.polarized a b) he he'
    _ = Intrinsic.ChernPairing.nativePolarizationForm A.polarized ((m₀).symm v) ((m₀).symm w) :=
      F.marking_polarization (D.pointTransport hP D.point).property.1 v w
    _ = _ := congrArg₂ (fun a b => Intrinsic.ChernPairing.nativePolarizationForm A.polarized a b) hxv hyw

def originComparison [IsGalois ℚ E] (hκ : κ.comp iota = P.μ) :
    RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison.NativePolarizedComparison A.polarized (D.fiberAt hP D.point).object.polarized where
  periods := originPeriodMap A hs hdegree D hP
  hodge := originPeriodMap_isHodgeMap A hs hdegree D hP hκ
  integral v := by
    have hlat : Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native (D.fiberAt hP D.point).object.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation (D.fiberAt hP D.point).object.polarized)) =
          Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (D.fiberAt hP D.point).model.model.abelian := by
      unfold Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods
      rfl
    rw [hlat]
    exact originPeriodMap_integral A hs hdegree D hP v
  polarization := originPeriodMap_polarization A hs hdegree D hP

theorem originComparison_marking [IsGalois ℚ E] (hκ : κ.comp iota = P.μ) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (originComparison A hs hdegree D hP hκ).periods ((m₀).symm v) =
      (D.fiberAt hP D.point).marking v :=
  originPeriodMap_marking A hs hdegree D hP v

def originIso [IsGalois ℚ E] (hκ : κ.comp iota = P.μ) :
    PEL.Objects.PELIso A (D.fiberAt hP D.point).object where
  polarized := (originComparison A hs hdegree D hP hκ).toLevelIso
    (Polarized.ComparisonMarkedLevel.polarizedComparison_level_of_rational_labels (originComparison A hs hdegree D hP hκ)
      (BallPELHecke.RealBallPELHecke.latticeLabel A hs hdegree) (BallPELHecke.RealBallPELHecke.latticeLabel_surjective A hs hdegree)
      (fun l => (m₀).symm l.val) (fun l => (D.fiberAt hP D.point).marking l.val) (N : ℝ)⁻¹
      (BallPELHecke.RealBallPELHecke.original_level A hs hdegree) (BallPELHecke.RealBallPELHecke.fiber_level A hs hdegree D hP D.point)
      (fun l => originComparison_marking A hs hdegree D hP hκ l.val))
  action a := by
    apply (originComparison A hs hdegree D hP hκ).algebraicIso_action A.action
      (D.fiberAt hP D.point).object.action
    intro b x
    exact LinearMap.congr_fun
      (Intrinsic.FieldMarkingBallTransport.NativeFieldMarking.transport_action A.polarized A.action (originalFieldMarking A hs hdegree)
        (D.fiberAt hP D.point).object.polarized (D.fiberAt hP D.point).object.action
        (D.fiberAt hP D.point).fieldMarking (LinearEquiv.refl E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) b) x

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELOrigin.RealBallPELHecke
