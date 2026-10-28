import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterBaseChangeValues

/-! # Parameter Character Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterBaseChange.Construction

noncomputable section

/-! The unit-valued character over a parameter scheme commutes with
arbitrary source base change through the canonical kernel comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme} (s : S' ⟶ S) (Q : Over S')

theorem parameterBaseChangeTestIso_projection (U : Over Q.left) :
    (ParameterBaseChange.Construction.parameterBaseChangeTestIso s Q U).inv ≫ (Over.map s).map (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U) =
      CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection ((Over.map s).obj Q) U :=
  Over.OverMorphism.ext (Category.id_comp _)

theorem parameterBaseChangeTestIso_unitValue (U : Over Q.left)
    (x : (Over.map s).obj ((Over.map Q.hom).obj U) ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map ((Over.map s).obj Q).hom).obj U)
        ((ParameterBaseChange.Construction.parameterBaseChangeTestIso s Q U).inv ≫ x) =
      CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map s).obj ((Over.map Q.hom).obj U)) x := by
  apply Units.ext
  rw [MultiplicativeUnitBaseChange.Construction.multiplicativeGroupUnitHom_value, MultiplicativeUnitBaseChange.Construction.multiplicativeGroupUnitHom_value]
  change ((𝟙 U.left ≫ x.left) ≫ CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S).appTop _ =
    (x.left ≫ CartierDuality.SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral S).appTop _
  rw [Category.id_comp]

variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

theorem parameterKernelCharacter_baseChange
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj Q)))
    (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((Over.pullback s).map f))) :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter ((Over.pullback s).map f) Q (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ) U z =
      CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f ((Over.map s).obj Q) χ U (z ≫ ParameterBaseChange.Construction.parameterBaseChangeKernelMap s Q f) := by
  let p := CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom ((Over.pullback s).map f) U z
  let d := CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f ((Over.map Q.hom).obj U) p
  let i := (ParameterBaseChange.Construction.parameterBaseChangeTestIso s Q U).inv
  let t := (Over.map s).map (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)
  let t0 := CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection ((Over.map s).obj Q) U
  let e : Over.mk t0 ⟶ Over.mk t := Over.homMk i (parameterBaseChangeTestIso_projection s Q U)
  have hn := χ.naturality_apply e.op d
  change χ.app (.op (Over.mk t0)) (i ≫ d) = i ≫ χ.app (.op (Over.mk t)) d at hn
  have hp := ParameterBaseChangePoints.Construction.parameterBaseChangeKernelPoint_original s Q f U z
  have hpoint := (congrArg (fun x => χ.app (.op (Over.mk t0)) x) hp).trans hn
  have hunit := (congrArg (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map ((Over.map s).obj Q).hom).obj U)) hpoint).trans
    (parameterBaseChangeTestIso_unitValue s Q U (χ.app (.op (Over.mk t)) d))
  exact (ParameterBaseChangeValues.Construction.baseChangedKernelCharacterSection_testValue s f Q χ ((Over.map Q.hom).obj U)
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U) p).trans hunit.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterBaseChange.Construction
