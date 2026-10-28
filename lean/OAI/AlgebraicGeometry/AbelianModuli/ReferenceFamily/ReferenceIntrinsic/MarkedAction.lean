import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.Marking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LiftDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Marked Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original reference marking intertwines the native algebraic
CM action. Its fixed ordered full levels are the actual native
exponentials of the prescribed rational division vectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeMarkedAction_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeMarkedAction_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceEmbedding_action (a : NumberField.RingOfIntegers E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.Maps.IntrinsicLinearMaps.linearLift (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) (M.nativeReferenceEmbedding v) =
      M.nativeReferenceEmbedding ((a : E) • v) := by
  have hl := congrArg (fun L : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian →ₗ[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian =>
      L (M.periodDifferential (F.periodEmbedding v)))
    (Intrinsic.LiftDifferential.IntrinsicLinearMaps.linearLift_eq_nativeDifferential (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)))
  exact hl.trans ((M.periodDifferential_action a (F.periodEmbedding v)).trans
    (congrArg M.periodDifferential (F.equivariant a v)))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceMarking_action (a : NumberField.RingOfIntegers E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) (M.nativeReferenceMarking v) =
      M.nativeReferenceMarking ((a : E) • v) :=
  Subtype.ext (M.nativeReferenceEmbedding_action a v)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.fixedFullLevel_native_reference (N : ℕ) [NeZero N] (v : P.lattice) :
    (((M.fixedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP N v)))).val =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
          ((N : ℝ)⁻¹ • (M.nativeReferenceMarking v.val).val) := by
  have he := M.periodDifferential_exp ((N : ℝ)⁻¹ • F.periodEmbedding v.val)
  have hs := (M.periodDifferential.toContinuousLinearMap.restrictScalars ℝ).map_smul
    (N : ℝ)⁻¹ (F.periodEmbedding v.val)
  exact (M.fixedFullLevel_reference N v).trans (he.symm.trans
    (congrArg (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) hs))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
