import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Choices

/-! # Choice Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction

noncomputable section

/-!
The full kernel attached to a tuple of supported subgroup choices. The
chosen factors and their opposite annihilators are indexed separately;
orthogonality of the torsion projectors gives the full geometric model.
There is no extra choice of opposite subgroups or kernel model in the data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
variable (n s : ℕ) (M : Fin s → Type u)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
variable (p q : Fin s → (A ⟶ A)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
variable {W : Over S} [GrpObj W]
variable (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W))
variable (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A n (M i) (p i) P)

abbrev KernelIndex (s : ℕ) := Fin s ⊕ Fin s

def choiceKernelProjector : KernelIndex s → (A ⟶ A) := Sum.elim p q

instance choiceKernelProjector_isMonHom (i : KernelIndex s) :
    IsMonHom (choiceKernelProjector s p q i) := by
  cases i <;> dsimp only [choiceKernelProjector, Sum.elim] <;> infer_instance

def choiceKernelFactor : KernelIndex s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P :=
  Sum.elim (fun i => (U i).val.subgroup)
    (fun i => OppositeKernel.Construction.oppositeKernel n (p i) (q i) (e i) (U i).val.subgroup)

theorem choiceKernelFactor_killed (i : KernelIndex s) :
    (choiceKernelFactor n s M p q e U i).KilledBy n := by
  cases i with
  | inl i => exact (U i).val.killed
  | inr i =>
      intro X t x hx
      obtain ⟨y, _, rfl⟩ := hx
      change (y ≫ OppositeKernel.Construction.torsionBlockInclusion n (q i)) ^ n = 1
      rw [← MonObj.comp_pow, OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]

theorem choiceKernelFactor_supported (i : KernelIndex s) :
    SubgroupFunctor.Construction.SupportedOn (choiceKernelFactor n s M p q e U i) (choiceKernelProjector s p q i) := by
  cases i with
  | inl i => exact (U i).property
  | inr i =>
      intro X t x hx
      obtain ⟨y, _, rfl⟩ := hx
      change (y ≫ OppositeKernel.Construction.torsionBlockInclusion n (q i)) ≫ q i = y ≫ OppositeKernel.Construction.torsionBlockInclusion n (q i)
      rw [Category.assoc, OppositeKernel.Construction.torsionBlockInclusion_supported]

/-- The factor models are obtained from the chosen subgroup's geometric
witness and from the constructed relative annihilator. -/
def choiceKernelFactor_models [Etale W.hom] [IsSeparated W.hom]
    (horth : ∀ i, Torsion.Groups.Construction.nativeTorsionMap n (q i) ≫ Torsion.Groups.Construction.nativeTorsionMap n (p i) = 1)
    (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧ Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    ∀ i, (choiceKernelFactor n s M p q e U i).Model := by
  intro i
  cases i with
  | inl i => exact Classical.choice (U i).val.geometric
  | inr i =>
      let R := Classical.choice (U i).val.geometric
      exact Classical.choice (OppositeKernel.Construction.oppositeKernel_and_product_models n (p i) (q i) (e i)
        (U i).val.subgroup R (U i).val.killed (U i).property (horth i) h_TorsionQuotient).1

/-- The full kernel, defined from the choices and the forced opposites. -/
def choiceFullKernel : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P :=
  Kernel.Tuples.Construction.tupleKernel (Fintype.card (KernelIndex s)) (fun j =>
    choiceKernelFactor n s M p q e U ((Fintype.equivFin (KernelIndex s)).symm j))

theorem choiceFullKernel_killed : (choiceFullKernel n s M p q e U).KilledBy n :=
  Kernel.Tuples.Construction.tupleKernel_killed _ _ n (fun j => choiceKernelFactor_killed n s M p q e U
    ((Fintype.equivFin (KernelIndex s)).symm j))

/-- Orthogonal torsion projectors give a model for the entire kernel;
none of its geometry is assumed as a property of the choice data. -/
def choiceFullKernel_model [Etale W.hom] [IsSeparated W.hom]
    (hsep : ∀ i j : KernelIndex s, i ≠ j →
      Torsion.Groups.Construction.nativeTorsionMap n (choiceKernelProjector s p q j) ≫
        Torsion.Groups.Construction.nativeTorsionMap n (choiceKernelProjector s p q i) = 1)
    (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧ Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    (choiceFullKernel n s M p q e U).Model := by
  let r := (Fintype.equivFin (KernelIndex s)).symm
  have horth i : Torsion.Groups.Construction.nativeTorsionMap n (q i) ≫ Torsion.Groups.Construction.nativeTorsionMap n (p i) = 1 :=
    hsep (.inl i) (.inr i) (by intro h; cases h)
  let R := choiceKernelFactor_models n s M p q e U horth h_TorsionQuotient
  exact Kernel.Assembly.Construction.separatedTorsionTuple_model n (Fintype.card (KernelIndex s))
    (fun j => choiceKernelFactor n s M p q e U (r j)) (fun j => R (r j))
    (fun j => choiceKernelProjector s p q (r j))
    (fun j => choiceKernelFactor_killed n s M p q e U (r j))
    (fun j => choiceKernelFactor_supported n s M p q e U (r j))
    (fun i j hij => hsep (r i) (r j) (fun h => hij (r.injective h)))

def blockChoicesBaseChange {Q : Over S} (b : Q ⟶ P) :
    ∀ i, SubgroupFunctor.Construction.SupportedChoice A n (M i) (p i) Q := fun i =>
  (SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i)).map b.op (U i)

theorem choiceKernelFactor_baseChange {Q : Over S} (b : Q ⟶ P) (i : KernelIndex s) :
    (choiceKernelFactor n s M p q e U i).baseChange b =
      choiceKernelFactor n s M p q e (blockChoicesBaseChange n s M p U b) i := by
  cases i with
  | inl i => rfl
  | inr i => exact OppositeKernel.Construction.oppositeKernel_baseChange n (p i) (q i) (e i) (U i).val.subgroup b

theorem choiceFullKernel_baseChange {Q : Over S} (b : Q ⟶ P) :
    (choiceFullKernel n s M p q e U).baseChange b =
      choiceFullKernel n s M p q e (blockChoicesBaseChange n s M p U b) := by
  unfold choiceFullKernel
  rw [Kernel.Tuples.Construction.tupleKernel_baseChange]
  congr 1
  funext j
  exact choiceKernelFactor_baseChange n s M p q e U b _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction
