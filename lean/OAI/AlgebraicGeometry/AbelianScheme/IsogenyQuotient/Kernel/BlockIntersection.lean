import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TuplePoints

/-! # Block Intersection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.BlockIntersection.Construction

noncomputable section

/-!
Intersecting the exact assembled kernel with a chosen projector block
recovers precisely the original chosen subgroup. Orthogonality excludes
all other factors, including the forced opposite annihilators.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u v

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  {I : Type v} [Fintype I] (s : ℕ) (r : Fin s ≃ I)
  (F : I → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)

theorem mem_tupleKernel_of_mem_factor (X : Over S) (t : X ⟶ P) (i : I)
    (x : X ⟶ A) (hx : x ∈ (F i).points X t) :
    x ∈ (Tuples.Construction.tupleKernel s (fun j => F (r j))).points X t := by
  classical
  apply (TuplePoints.Construction.tupleKernel_points_iff_equiv s r F X t x).mpr
  refine ⟨Pi.mulSingle i x, ?_, by simp⟩
  intro j
  by_cases hj : j = i
  · subst j
    simpa using hx
  · simpa only [Pi.mulSingle_eq_of_ne hj] using (F j).points X t |>.one_mem

theorem tupleKernel_projector_mem_factor (p : I → (A ⟶ A)) [∀ i, IsMonHom (p i)]
    (hsupport : ∀ i, SubgroupFunctor.Construction.SupportedOn (F i) (p i))
    (hdisjoint : ∀ i j, i ≠ j → Tuples.Construction.AnnihilatedBy (F j) (p i))
    (X : Over S) (t : X ⟶ P) (i : I) (x : X ⟶ A)
    (hx : x ∈ (Tuples.Construction.tupleKernel s (fun j => F (r j))).points X t) :
    x ≫ p i ∈ (F i).points X t := by
  classical
  obtain ⟨y, hy, rfl⟩ := (TuplePoints.Construction.tupleKernel_points_iff_equiv s r F X t x).mp hx
  have he : (∏ j, y j) ≫ p i = y i := by
    calc
      _ = ∏ j, y j ≫ p i := map_prod (IsMonHom.monoidHom (p i) X) y Finset.univ
      _ = y i ≫ p i := Finset.prod_eq_single i
        (fun j _ hji => hdisjoint i j hji.symm X t (y j) (hy j)) (by simp)
      _ = y i := hsupport i X t (y i) (hy i)
  rw [he]
  exact hy i

theorem tupleKernel_block_membership (p : I → (A ⟶ A)) [∀ i, IsMonHom (p i)]
    (hsupport : ∀ i, SubgroupFunctor.Construction.SupportedOn (F i) (p i))
    (hdisjoint : ∀ i j, i ≠ j → Tuples.Construction.AnnihilatedBy (F j) (p i))
    (X : Over S) (t : X ⟶ P) (i : I) (x : X ⟶ A) (hx : x ≫ p i = x) :
    x ∈ (Tuples.Construction.tupleKernel s (fun j => F (r j))).points X t ↔ x ∈ (F i).points X t := by
  constructor
  · intro h
    have hh := tupleKernel_projector_mem_factor s r F p hsupport hdisjoint X t i x h
    rwa [hx] at hh
  · exact mem_tupleKernel_of_mem_factor s r F X t i x

variable (n m : ℕ) (M : Fin m → Type u)
  [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
  (p q : Fin m → (A ⟶ A)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
  {W : Over S} [GrpObj W]
  (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W))
  (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A n (M i) (p i) P)
  (hsep : ∀ i j : ChoiceKernel.Construction.KernelIndex m, i ≠ j →
    Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector m p q j) ≫
      Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector m p q i) = 1)

include hsep in
theorem choiceFullKernel_chosen_membership (X : Over S) (t : X ⟶ P)
    (i : Fin m) (x : X ⟶ A) (hx : x ≫ p i = x) :
    x ∈ (ChoiceKernel.Construction.choiceFullKernel n m M p q e U).points X t ↔ x ∈ (U i).val.subgroup.points X t := by
  exact tupleKernel_block_membership (Fintype.card (ChoiceKernel.Construction.KernelIndex m))
    (Fintype.equivFin (ChoiceKernel.Construction.KernelIndex m)).symm
    (ChoiceKernel.Construction.choiceKernelFactor n m M p q e U) (ChoiceKernel.Construction.choiceKernelProjector m p q)
    (ChoiceKernel.Construction.choiceKernelFactor_supported n m M p q e U)
    (fun i j hij => Assembly.Construction.annihilatedBy_of_torsion_projector_separation n
      (ChoiceKernel.Construction.choiceKernelFactor n m M p q e U j)
      (ChoiceKernel.Construction.choiceKernelProjector m p q i) (ChoiceKernel.Construction.choiceKernelProjector m p q j)
      (ChoiceKernel.Construction.choiceKernelFactor_killed n m M p q e U j)
      (ChoiceKernel.Construction.choiceKernelFactor_supported n m M p q e U j) (hsep i j hij)) X t (.inl i) x hx

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.BlockIntersection.Construction
