import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterBaseChangeValues

/-! # Parameter Base Change Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChangeValues.Construction

noncomputable section

/-! Actual kernel-character values after base change are retained on every
further parameter test, with its original structural morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

theorem baseChangedKernelCharacterSection_testValue (Q : Over S')
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj Q)))
    (U : Over S') (t : U ⟶ Q) (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom U
      ((CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ).app (.op (Over.mk t)) z) =
      CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map s).obj U)
        ((χ.app (.op (Over.mk ((Over.map s).map t)))) (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f U z)) := by
  have hl := CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict t (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ) z
  have hn := CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection_natural s f t χ
  have hr := CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict ((Over.map s).map t) χ (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f U z)
  exact (congrArg (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom U) hl.symm).trans
    ((congrArg
      (fun ψ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))).obj.obj (.op U) =>
        CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom U
          (CartierDuality.Evaluation.Construction.CharacterEvaluation.value
            (F := yonedaGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f))))
            (K := yonedaGrp.obj (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S')) ψ z)) hn).trans
      ((CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection_unitValue s f U _ z).trans
        (congrArg (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map s).obj U)) hr)))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChangeValues.Construction
