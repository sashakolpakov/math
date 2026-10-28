import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslatedConormal

/-! # Conormal Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ConormalOperations

noncomputable section

section

/-! At every complex coefficient point, the previously constructed
affine-chart conormal bijection is the actual complex-linear tangent
map obtained by translating that point to the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [GrpObj X]
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    [Algebra B ℂ] [IsScalarTower ℂ B ℂ] (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ X) [IsOpenImmersion i.left]

local notation "p₀" => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i (IsScalarTower.toAlgHom ℂ B ℂ)

def complexPointConormalLinear : Derivation ℂ B ℂ →ₗ[ℂ] (Constructed.IdentityConormal.constructedIdentityConormal ℂ X →ₗ[ℂ] ℂ) :=
  (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear X).toLinearMap.comp
    ((Intrinsic.GroupPointSubtraction.nativeGroupPointSubtraction X p₀).comp (Intrinsic.ChartCoefficientDerivative.nativeChartCoefficientDerivative X B i).symm.toLinearMap)

theorem complexPointConormalLinear_apply (d : Derivation ℂ B ℂ) :
    complexPointConormalLinear X B i d = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i d := by
  let v := (Intrinsic.ChartCoefficientDerivative.nativeChartCoefficientDerivative X B i).symm d
  let c := Affine.IntrinsicCoefficientPoint.openAffineLiftReference ℂ ℂ X (Affine.ChartCoefficientConormal.affineChartCoefficientPoint ℂ B ℂ X i)
  let f := (Affine.ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B ℂ X i).symm d
  have hred : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ f.val = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ c :=
    f.property.trans (Affine.IntrinsicCoefficientPoint.openAffineLiftReference_reduction ℂ ℂ X (Affine.ChartCoefficientConormal.affineChartCoefficientPoint ℂ B ℂ X i)).symm
  let g := (⟨f.val, hred⟩ : {f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X //
    Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ c})
  have hv := (Intrinsic.ChartCoefficientDerivative.nativeChartCoefficientDerivative X B i).apply_symm_apply d
  have hf : g.val = (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p₀ v).val) :=
    (congrArg (fun d' => ((Affine.ChartCoefficientConormal.affineChartCoefficientLiftDerivationEquiv ℂ B ℂ X i).symm d').val) hv.symm).trans
      (Intrinsic.ChartCoefficientDerivative.nativeChartCoefficientDerivative_lift X B i v)
  have hc : c = (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from toUnit (LieRanks.dualNumberTest ℂ) ≫ p₀) :=
    Affine.IntrinsicCoefficientPoint.nativeAffineCoefficientPoint_constant X B i (IsScalarTower.toAlgHom ℂ B ℂ)
  exact (Intrinsic.TranslatedConormal.nativeTranslatedConormal_eq X p₀ v c hc g hf).symm

def complexPointConormalLinearEquiv : Derivation ℂ B ℂ ≃ₗ[ℂ] (Constructed.IdentityConormal.constructedIdentityConormal ℂ X →ₗ[ℂ] ℂ) := by
  apply LinearEquiv.ofBijective (complexPointConormalLinear X B i)
  constructor
  · intro d e h
    apply (Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i).injective
    exact (complexPointConormalLinear_apply X B i d).symm.trans
      (h.trans (complexPointConormalLinear_apply X B i e))
  · intro q
    let d := (Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i).symm q
    exact ⟨d, (complexPointConormalLinear_apply X B i d).trans
      ((Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i).apply_symm_apply q)⟩

theorem complexPointConormalLinearEquiv_apply (d : Derivation ℂ B ℂ) :
    complexPointConormalLinearEquiv X B i d = Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i d :=
  complexPointConormalLinear_apply X B i d

end

/-! The actual conormal coordinate function preserves addition and
complex scalar multiplication at every complex coefficient point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [GrpObj X]
    (B : CommAlgCat ℂ) [IsDomain B] [Algebra.Smooth ℂ B]
    [Algebra B ℂ] [IsScalarTower ℂ B ℂ] (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ X) [IsOpenImmersion i.left]

theorem complexConormal_add (d e : Derivation ℂ B ℂ) :
    Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (d + e) =
      Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i d + Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i e :=
  (complexPointConormalLinearEquiv_apply X B i (d + e)).symm.trans
    (((complexPointConormalLinearEquiv X B i).map_add d e).trans
      (congrArg₂ (· + ·) (complexPointConormalLinearEquiv_apply X B i d) (complexPointConormalLinearEquiv_apply X B i e)))

theorem complexConormal_smul (c : ℂ) (d : Derivation ℂ B ℂ) :
    Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i (c • d) = c • Affine.ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B ℂ X i d :=
  (complexPointConormalLinearEquiv_apply X B i (c • d)).symm.trans
    (((complexPointConormalLinearEquiv X B i).map_smul c d).trans
      (congrArg (fun f => c • f) (complexPointConormalLinearEquiv_apply X B i d)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ConormalOperations
