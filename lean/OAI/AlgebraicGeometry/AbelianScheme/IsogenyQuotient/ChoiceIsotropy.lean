import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitIsotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TupleImages
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel

/-! # Choice Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceIsotropy.Construction

noncomputable section

/-!
Apply the full split calculation to the exact kernel used by the quotient
construction. Pullback to native torsion and inclusion into the abelian
scheme are compared on all test schemes. CartierDuality's double-annihilator clauses
are explicit conditional inputs; the pairing still needs identification
with the canonical polarization-induced pairing.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (n s : ℕ) (M : Fin s → Type u)
  [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
  (p q : Fin s → (A ⟶ A)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
  {W : Over S} [GrpObj W] [IsCommMonObj W]
  (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W))
  (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A n (M i) (p i) P)

abbrev choiceTorsionProjector (j : ChoiceKernel.Construction.KernelIndex s) :
    Torsion.Groups.Construction.nativeTorsionScheme A n ⟶ Torsion.Groups.Construction.nativeTorsionScheme A n :=
  Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p q j)

variable (horth : ∀ i j : ChoiceKernel.Construction.KernelIndex s, i ≠ j →
    choiceTorsionProjector n s p q i ≫ choiceTorsionProjector n s p q j = 1)
  (hcomplete : (∏ i, choiceTorsionProjector n s p q i) = 𝟙 (Torsion.Groups.Construction.nativeTorsionScheme A n))

def choiceTorsionPairing : Annihilator.Construction.SchemeBicharacter
    (A := Torsion.Groups.Construction.nativeTorsionScheme A n) (B := Torsion.Groups.Construction.nativeTorsionScheme A n) (W := W) :=
  SplitIsotropy.Construction.fullSplitSchemePairing (choiceTorsionProjector n s p q) horth hcomplete e

def choiceTorsionFullKernel : TorsionQuotient.SubgroupFunctor.RelativeSubgroup (Torsion.Groups.Construction.nativeTorsionScheme A n) P := by
  let H : ∀ i : Fin s, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (OppositeKernel.Construction.torsionBlock n (p i)) P :=
    fun i => SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n (p i)) (U i).val.subgroup
  exact SplitIsotropy.Construction.fullSplitRelativeKernel (choiceTorsionProjector n s p q) horth hcomplete e H

omit [IsCommMonObj W] in
theorem choiceTorsionFullKernel_image :
    SubgroupTransport.Construction.relativeSubgroupImage (Torsion.Groups.Construction.nativeTorsionInclusion A n)
        (choiceTorsionFullKernel n s M p q e U horth hcomplete) =
      ChoiceKernel.Construction.choiceFullKernel n s M p q e U := by
  let H := fun i => SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n (p i)) (U i).val.subgroup
  have hf (i : ChoiceKernel.Construction.KernelIndex s) :
      SubgroupTransport.Construction.relativeSubgroupImage (Torsion.Groups.Construction.nativeTorsionInclusion A n)
        (SubgroupTransport.Construction.relativeSubgroupImage (BlockGroups.Construction.fixedPointInclusion (choiceTorsionProjector n s p q i))
          (SplitIsotropy.Construction.splitKernelBlockFamily (choiceTorsionProjector n s p q) e H i)) =
        ChoiceKernel.Construction.choiceKernelFactor n s M p q e U i := by
    rw [TupleImages.Construction.relativeSubgroupImage_comp]
    cases i with
    | inl i =>
        exact OppositeKernel.Construction.supportedTorsionBlock_image n (p i) (U i).val.subgroup
          (U i).val.killed (U i).property
    | inr i => rfl
  let r := (Fintype.equivFin (ChoiceKernel.Construction.KernelIndex s)).symm
  let F := fun i : ChoiceKernel.Construction.KernelIndex s => SubgroupTransport.Construction.relativeSubgroupImage
    (BlockGroups.Construction.fixedPointInclusion (choiceTorsionProjector n s p q i))
    (SplitIsotropy.Construction.splitKernelBlockFamily (choiceTorsionProjector n s p q) e H i)
  calc
    _ = SubgroupTransport.Construction.relativeSubgroupImage (Torsion.Groups.Construction.nativeTorsionInclusion A n)
        (Kernel.Tuples.Construction.tupleKernel (Fintype.card (ChoiceKernel.Construction.KernelIndex s)) (fun k => F (r k))) :=
      congrArg (SubgroupTransport.Construction.relativeSubgroupImage (Torsion.Groups.Construction.nativeTorsionInclusion A n))
        (SplitIsotropy.Construction.fullSplitRelativeKernel_eq_tuple (choiceTorsionProjector n s p q)
          horth hcomplete e H (Fintype.card (ChoiceKernel.Construction.KernelIndex s)) r)
    _ = Kernel.Tuples.Construction.tupleKernel (Fintype.card (ChoiceKernel.Construction.KernelIndex s))
        (fun k => SubgroupTransport.Construction.relativeSubgroupImage (Torsion.Groups.Construction.nativeTorsionInclusion A n) (F (r k))) :=
      TupleImages.Construction.relativeSubgroupImage_tupleKernel _ _ _
    _ = _ := congrArg (Kernel.Tuples.Construction.tupleKernel (Fintype.card (ChoiceKernel.Construction.KernelIndex s))) (funext (fun k => hf (r k)))

omit [IsCommMonObj W] in
theorem choiceFullKernel_pullback_torsion :
    SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (ChoiceKernel.Construction.choiceFullKernel n s M p q e U) =
      choiceTorsionFullKernel n s M p q e U horth hcomplete := by
  rw [← choiceTorsionFullKernel_image n s M p q e U horth hcomplete]
  ext X t x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have he : y = x := (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A n)).mp hxy
    exact he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Self-annihilation of the exact universal quotient kernel, viewed
inside native torsion, follows from the per-block CartierDuality conclusion. -/
theorem choiceFullKernel_self_annihilating_of_CartierDuality
    (h_CartierDuality : ∀ i, (e i).flip.relativeAnnihilator
      ((e i).relativeAnnihilator
        (SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n (p i)) (U i).val.subgroup)) =
      SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n (p i)) (U i).val.subgroup) :
    (choiceTorsionPairing n s p q e horth hcomplete).relativeAnnihilator
        (SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (ChoiceKernel.Construction.choiceFullKernel n s M p q e U)) =
      SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (ChoiceKernel.Construction.choiceFullKernel n s M p q e U) := by
  rw [choiceFullKernel_pullback_torsion n s M p q e U horth hcomplete]
  exact SplitIsotropy.Construction.fullSplitRelativeKernel_self_annihilating_of_CartierDuality _ _ _ _ _ h_CartierDuality

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceIsotropy.Construction
