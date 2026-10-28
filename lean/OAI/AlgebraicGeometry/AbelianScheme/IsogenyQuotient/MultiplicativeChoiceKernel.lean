import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedBlockChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction

/-! # Multiplicative Choice Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeChoiceKernel.Construction

noncomputable section

/-!
Actual G_m-valued torsion pairings take values in the common native
root-of-unity scheme. Changing to that target leaves the original
chosen/opposite kernel unchanged and constructs its finite subgroup model.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (n s : ℕ) (p r : Fin s → (A ⟶ A)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
  (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i))
    (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

def blockPairingsToRoots : ∀ i, Annihilator.Construction.SchemeBicharacter
    (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i)) (W := Multiplicative.Construction.rootsOfUnityScheme S n) :=
  fun i => (e i).torsionTarget n (SupportedBlockChoices.Construction.torsionBlock_identity_killed n (p i))

theorem oppositeKernel_roots_target (i : Fin s) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    OppositeKernel.Construction.oppositeKernel n (p i) (r i) (blockPairingsToRoots n s p r e i) F =
      OppositeKernel.Construction.oppositeKernel n (p i) (r i) (e i) F :=
  congrArg (SubgroupTransport.Construction.relativeSubgroupImage (OppositeKernel.Construction.torsionBlockInclusion n (r i)))
    ((e i).torsionTarget_relativeAnnihilator n (SupportedBlockChoices.Construction.torsionBlock_identity_killed n (p i))
      (SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n (p i)) F))

variable (M : Fin s → Type u) [∀ i, AddCommGroup (M i)]
  [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
  (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A n (M i) (p i) P)

theorem choiceFullKernel_roots_target :
    ChoiceKernel.Construction.choiceFullKernel n s M p r (blockPairingsToRoots n s p r e) U = ChoiceKernel.Construction.choiceFullKernel n s M p r e U := by
  have hf (i : ChoiceKernel.Construction.KernelIndex s) : ChoiceKernel.Construction.choiceKernelFactor n s M p r (blockPairingsToRoots n s p r e) U i =
      ChoiceKernel.Construction.choiceKernelFactor n s M p r e U i := by
    cases i with
    | inl i => rfl
    | inr i => exact oppositeKernel_roots_target n s p r e i (U i).val.subgroup
  exact congrArg (Kernel.Tuples.Construction.tupleKernel (Fintype.card (ChoiceKernel.Construction.KernelIndex s)))
    (funext (fun k => hf ((Fintype.equivFin (ChoiceKernel.Construction.KernelIndex s)).symm k)))

def multiplicativeChoiceFullKernel_model
    {K : Type u} [Field K] [CharZero K] (base : S ⟶ Spec (.of K)) (hn : 0 < n)
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (hsep : ∀ i j : ChoiceKernel.Construction.KernelIndex s, i ≠ j →
      Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p r j) ≫
        Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p r i) = 1) :
    (ChoiceKernel.Construction.choiceFullKernel n s M p r e U).Model := by
  let : Etale (Multiplicative.Construction.rootsOfUnityScheme S n).hom := Multiplicative.Construction.rootsOfUnityScheme_etale S n
    (Unit.Construction.positive_integer_unit_on_characteristic_zero_base base n hn)
  let : IsSeparated (Multiplicative.Construction.rootsOfUnityScheme S n).hom := Multiplicative.Construction.rootsOfUnityScheme_separated S n
  let R := ChoiceKernel.Construction.choiceFullKernel_model n s M p r (blockPairingsToRoots n s p r e) U hsep
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A) base n hn Torsion.Construction.verified_TorsionQuotientInput)
  exact choiceFullKernel_roots_target n s p r e M U ▸ R

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeChoiceKernel.Construction
