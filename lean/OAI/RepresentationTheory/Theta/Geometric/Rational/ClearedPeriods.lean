import OAI.RepresentationTheory.Theta.Geometric.Reference.PeriodMapDifferential
import OAI.RepresentationTheory.Theta.Geometric.Reference.ModelTransport
import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodCM

/-! # Cleared Periods -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The actual rational-period action of an algebraic map is determined
by the original rational SU matrix in the fixed quotient coordinates. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU) (x : D.domain)
    (F : D.ReferenceAnalyticFiber x) (G : D.ReferenceAnalyticFiber (D.rationalPeriodPoint g x))

def Data.ActiveHeckeThetaData.rationalReferenceLinear : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceTangent s →ₗ[ℂ] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceTangent s :=
  (G.periodComparison D hg).toLinearMap.comp
    ((D.rationalPeriodLinear g x).comp (F.periodComparison D hg).symm.toLinearMap)

theorem Data.ActiveHeckeThetaData.rationalReferenceLinear_embedding (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Data.ActiveHeckeThetaData.rationalReferenceLinear hg g x F G ((F.toNativeReference D).periodEmbedding v) =
      (G.toNativeReference D).periodEmbedding (D.rationalLinear g v) := by
  have hF : F.periodComparison D hg (D.periodReferenceEmbedding x.val v) =
      (F.toNativeReference D).periodEmbedding v :=
    F.periodComparison_projection D hg _
  change G.periodComparison D hg
    (D.rationalPeriodLinear g x ((F.periodComparison D hg).symm
      ((F.toNativeReference D).periodEmbedding v))) = _
  rw [← hF, LinearEquiv.symm_apply_apply, D.rationalPeriodLinear_reference hg]
  exact G.periodComparison_projection D hg _

variable (M : D.PeriodModel hg x) (N : D.PeriodModel hg (D.rationalPeriodPoint g x))
    (f : M.abelian.toOver ⟶ N.abelian.toOver) [IsMonHom f]
    (hf : ∀ v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s),
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period (QuotientAddGroup.mk v)) =
        N.period (QuotientAddGroup.mk (D.rationalPeriodLinear g x v)))

include hf in
omit [IsMonHom f] in
theorem Data.ActiveHeckeThetaData.rationalReference_vectorPeriod (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceTangent s) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ((M.toNativeReferenceModel F).vectorPeriod v) =
      (N.toNativeReferenceModel G).vectorPeriod (Data.ActiveHeckeThetaData.rationalReferenceLinear hg g x F G v) := by
  obtain ⟨u, rfl⟩ := (F.periodComparison D hg).surjective v
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
    ((M.toNativeReferenceModel F).period (QuotientAddGroup.mk (F.periodComparison D hg u))) = _
  rw [M.toNativeReferenceModel_vectorPeriod, hf]
  change N.period (QuotientAddGroup.mk (D.rationalPeriodLinear g x u)) =
    (N.toNativeReferenceModel G).period (QuotientAddGroup.mk
      (G.periodComparison D hg (D.rationalPeriodLinear g x
        ((F.periodComparison D hg).symm (F.periodComparison D hg u)))))
  rw [LinearEquiv.symm_apply_apply, N.toNativeReferenceModel_vectorPeriod]

include hf in
theorem Data.ActiveHeckeThetaData.rationalReference_rationalPeriods (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f ((M.toNativeReferenceModel F).nativeReferenceMarking v) =
      (N.toNativeReferenceModel G).nativeReferenceMarking (D.rationalLinear g v) :=
  Reference.PeriodMapDifferential.reference_rationalPeriod_action (M.toNativeReferenceModel F) (N.toNativeReferenceModel G)
    f (Data.ActiveHeckeThetaData.rationalReferenceLinear hg g x F G) (Data.ActiveHeckeThetaData.rationalReference_vectorPeriod hg g x F G M N f hf)
    (D.rationalLinear g).toLinearMap (Data.ActiveHeckeThetaData.rationalReferenceLinear_embedding hg g x F G) v

end

/-! Prescribed denominator clearing retains the literal rational-period
map in the original reference markings. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    (hg : D.pel.HasIntegralModelGeometry) (g : D.RationalSU) (x : D.domain)
    (F : D.ReferenceAnalyticFiber x) (G : D.ReferenceAnalyticFiber (D.rationalPeriodPoint g x))

variable (n : ℕ)
    (M : D.PeriodModel hg x) (N : D.PeriodModel hg (D.rationalPeriodPoint g x))
    (f : M.abelian.toOver ⟶ N.abelian.toOver) [IsMonHom f]
    (hf : ∀ v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s),
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period (QuotientAddGroup.mk v)) =
        N.period (QuotientAddGroup.mk ((q : ℤ) ^ n • D.rationalPeriodLinear g x v)))

include hf in
omit [IsMonHom f] in
theorem Data.ActiveHeckeThetaData.clearedReference_vectorPeriod (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceTangent s) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ((M.toNativeReferenceModel F).vectorPeriod v) =
      (N.toNativeReferenceModel G).vectorPeriod ((q : ℤ) ^ n • Data.ActiveHeckeThetaData.rationalReferenceLinear hg g x F G v) := by
  obtain ⟨u, rfl⟩ := (F.periodComparison D hg).surjective v
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
    ((M.toNativeReferenceModel F).period (QuotientAddGroup.mk (F.periodComparison D hg u))) = _
  rw [M.toNativeReferenceModel_vectorPeriod, hf]
  have he : (q : ℤ) ^ n • Data.ActiveHeckeThetaData.rationalReferenceLinear hg g x F G (F.periodComparison D hg u) =
      G.periodComparison D hg ((q : ℤ) ^ n • D.rationalPeriodLinear g x u) := by
    change (q : ℤ) ^ n • G.periodComparison D hg
      (D.rationalPeriodLinear g x ((F.periodComparison D hg).symm (F.periodComparison D hg u))) = _
    rw [LinearEquiv.symm_apply_apply, map_zsmul]
  rw [he]
  exact (N.toNativeReferenceModel_vectorPeriod G _).symm

include hf in
theorem Data.ActiveHeckeThetaData.clearedReference_rationalPeriods (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f ((M.toNativeReferenceModel F).nativeReferenceMarking v) =
      (N.toNativeReferenceModel G).nativeReferenceMarking ((q : ℤ) ^ n • D.rationalLinear g v) := by
  apply Reference.PeriodMapDifferential.reference_rationalPeriod_action (M.toNativeReferenceModel F) (N.toNativeReferenceModel G)
    f ((q : ℤ) ^ n • Data.ActiveHeckeThetaData.rationalReferenceLinear hg g x F G)
    (Data.ActiveHeckeThetaData.clearedReference_vectorPeriod hg g x F G n M N f hf)
    ((q : ℤ) ^ n • (D.rationalLinear g).toLinearMap) ?_ v
  intro u
  change (q : ℤ) ^ n • Data.ActiveHeckeThetaData.rationalReferenceLinear hg g x F G ((F.toNativeReference D).periodEmbedding u) =
    (G.toNativeReference D).periodEmbedding ((q : ℤ) ^ n • D.rationalLinear g u)
  rw [Data.ActiveHeckeThetaData.rationalReferenceLinear_embedding, map_zsmul]

end

end OAI.RepresentationTheory.Theta.Geometric
