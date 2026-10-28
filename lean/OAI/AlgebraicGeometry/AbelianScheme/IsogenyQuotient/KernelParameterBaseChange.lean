import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.KernelProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel

/-! # Kernel Parameter Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KernelParameterBaseChange.Construction

noncomputable section

/-! The whole chosen-plus-opposite kernel commutes with actual parameter
pullback. The local choices and pairings are constructed from the originals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (P : Over S)
  (n s : ℕ) (M : Fin s → Type) [∀ i, AddCommGroup (M i)]
  [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
  (p q : Fin s → (A.scheme ⟶ A.scheme)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
  (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (q i))
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
  (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A.scheme n (M i) (p i) P)

def blockChoicesOverParameter :
    ∀ i, SubgroupFunctor.Construction.SupportedChoice (A.pullback P.hom).scheme n (M i) ((Over.pullback P.hom).map (p i))
      (Over.mk (𝟙 P.left)) := fun i => Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter A P n (M i) (p i) (U i)

set_option backward.isDefEq.respectTransparency false in
theorem choiceKernelFactor_parameterBaseChange (i : ChoiceKernel.Construction.KernelIndex s) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P (ChoiceKernel.Construction.choiceKernelFactor n s M p q e U i) =
      ChoiceKernel.Construction.choiceKernelFactor n s M (fun j => (Over.pullback P.hom).map (p j))
        (fun j => (Over.pullback P.hom).map (q j))
        (fun j => Intrinsic.BlockPairingBaseChange.Construction.nativeBlockPairingPullback A (p j) (q j) n P.hom (e j))
        (blockChoicesOverParameter A P n s M p U) i := by
  cases i with
  | inl i => rfl
  | inr i => exact Intrinsic.BlockPairingBaseChange.Construction.oppositeKernel_parameterBaseChange A (p i) (q i) n P (e i) (U i).val.subgroup

set_option backward.isDefEq.respectTransparency false in
theorem choiceFullKernel_parameterBaseChange :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P (ChoiceKernel.Construction.choiceFullKernel n s M p q e U) =
      ChoiceKernel.Construction.choiceFullKernel n s M (fun j => (Over.pullback P.hom).map (p j))
        (fun j => (Over.pullback P.hom).map (q j))
        (fun j => Intrinsic.BlockPairingBaseChange.Construction.nativeBlockPairingPullback A (p j) (q j) n P.hom (e j))
        (blockChoicesOverParameter A P n s M p U) := by
  unfold ChoiceKernel.Construction.choiceFullKernel
  rw [Parameter.KernelProducts.Construction.relativeSubgroupOverParameter_tuple]
  congr 1
  funext j
  exact choiceKernelFactor_parameterBaseChange A P n s M p q e U _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KernelParameterBaseChange.Construction
