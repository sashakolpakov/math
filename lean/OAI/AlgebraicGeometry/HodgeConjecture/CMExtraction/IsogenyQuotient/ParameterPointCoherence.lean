import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterGroupPoints

/-! # Parameter Point Coherence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterPointCoherence

noncomputable section

/-! The canonical iterated-pullback comparison has the same original
group point on every test. Relative subgroup membership is invariant
under the resulting identity comparison of original-base tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction
open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterGroupPoints.Construction.KernelCharacters

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {P Q : Over S} (c : P ⟶ Q) (U : Over P.left)
  (z : U ⟶ (A.pullback P.hom).scheme)

theorem parameter_factor_original_point :
    A.baseChangePointsMulEquiv Q.hom ((Over.map c.left).obj U)
      ((A.pullback Q.hom).baseChangePointsMulEquiv c.left U
        (z ≫ (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A c.left Q.hom P.hom c.w).hom)) =
      (AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso c U).hom ≫ A.baseChangePointsMulEquiv P.hom U z := by
  apply Over.OverMorphism.ext
  change ((z.left ≫ (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A c.left Q.hom P.hom c.w).hom.left) ≫
    pullback.fst (pullback.snd A.scheme.hom Q.hom) c.left) ≫ pullback.fst A.scheme.hom Q.hom =
      (𝟙 U.left) ≫ (z.left ≫ pullback.fst A.scheme.hom P.hom)
  have he := congrArg (fun f => f.left)
    (HeckeCycles.BaseChangeSquare.CM.groupFactor_hom c.left Q.hom P.hom c.w A)
  have hp := (congrArg (fun f => f ≫
      pullback.fst (pullback.snd A.scheme.hom Q.hom) c.left ≫ pullback.fst A.scheme.hom Q.hom) he).trans
    (HeckeCycles.Source.SquareProjection.CM.factor_hom_projection c.left Q.hom P.hom c.w A.scheme)
  exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    ((congrArg (fun f => z.left ≫ f) hp).trans (Category.id_comp _).symm))

theorem parameter_test_projection :
    (AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso c U).hom ≫ (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U ≫ c) =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q ((Over.map c.left).obj U) := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

theorem parameter_factor_membership (H : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme Q) :
    A.baseChangePointsMulEquiv Q.hom ((Over.map c.left).obj U)
      ((A.pullback Q.hom).baseChangePointsMulEquiv c.left U
        (z ≫ (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A c.left Q.hom P.hom c.w).hom)) ∈
        H.points ((Over.map Q.hom).obj ((Over.map c.left).obj U))
          (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q ((Over.map c.left).obj U)) ↔
      A.baseChangePointsMulEquiv P.hom U z ∈
        (H.baseChange c).points ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U) := by
  rw [parameter_factor_original_point]
  change (AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso c U).hom ≫ A.baseChangePointsMulEquiv P.hom U z ∈
      H.points _ (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q ((Over.map c.left).obj U)) ↔
    A.baseChangePointsMulEquiv P.hom U z ∈ H.points _ (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U ≫ c)
  rw [← parameter_test_projection c U]
  exact AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.relativeSubgroup_membership_iso H (AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso c U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U ≫ c)
    (A.baseChangePointsMulEquiv P.hom U z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterPointCoherence
