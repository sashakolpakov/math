import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeUnitBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Character Base Change Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterBaseChangeValues

noncomputable section

/-! Restrict an actual internal-Hom character through the native kernel
base-change isomorphism, retaining its original values on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

def nativeKernelBaseChangeInverseGroup :
    Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) ⟶
      (Over.pullback s).mapGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) := by
  exact @Grp.homMk (Over S') _ _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))
    ((Over.pullback s).mapGrp.obj (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.kernelBaseChangeIso_inv_isMonHom s f)

def baseChangedKernelCharacterNat :
    (Over.map s).op ⋙ (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj ⟶
      (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))).obj :=
  (CartierDuality.CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).hom ≫
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (nativeKernelBaseChangeInverseGroup s f)).hom

def baseChangedKernelCharacterSection (Q : Over S')
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj Q))) :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))).obj.obj (.op Q) :=
  (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (nativeKernelBaseChangeInverseGroup s f)).hom.app (.op Q)
    ((CartierDuality.CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).hom.app (.op Q) χ)

theorem baseChangedKernelCharacterSection_natural {P Q : Over S'} (t : P ⟶ Q)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj Q))) :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)))).obj.map t.op
        (baseChangedKernelCharacterSection s f Q χ) =
      baseChangedKernelCharacterSection s f P
        ((CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map ((Over.map s).map t).op χ) := by
  let b := (CartierDuality.CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).hom
  let r := (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (nativeKernelBaseChangeInverseGroup s f)).hom
  have hr := r.naturality_apply t.op (b.app (.op Q) χ)
  have hb := b.naturality_apply t.op χ
  exact hr.symm.trans (congrArg (r.app (.op P)) hb.symm)

theorem baseChangedKernelCharacterSection_value (Q : Over S')
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj Q)))
    (z : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) :
    CartierDuality.Evaluation.Construction.CharacterEvaluation.value (baseChangedKernelCharacterSection s f Q χ) z =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q
        (CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f Q z)) :=
  CartierDuality.EvaluationBaseChange.Construction.Schemes.characterBaseChange_value s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) Q χ
    (z ≫ (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv)

theorem baseChangedKernelCharacterSection_unitValue (Q : Over S')
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj Q)))
    (z : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) :
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q
      (CartierDuality.Evaluation.Construction.CharacterEvaluation.value (baseChangedKernelCharacterSection s f Q χ) z) =
      CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map s).obj Q)
        (CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f Q z)) :=
  (congrArg (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q) (baseChangedKernelCharacterSection_value s f Q χ z)).trans
    (MultiplicativeUnitBaseChange.Construction.multiplicativeGroupUnitHom_baseChange s Q _)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterBaseChangeValues
