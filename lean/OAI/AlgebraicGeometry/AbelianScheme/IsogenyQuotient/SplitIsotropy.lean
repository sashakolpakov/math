import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Annihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairedProjectors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProjectorKernel

/-! # Split Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitIsotropy.Construction

noncomputable section

/-!
Assemble all chosen/opposite pairs in the complete native torsion group.
The total pairing is a scheme map, and CartierDuality's double-annihilator conclusion
on each pair proves self-annihilation of the assembled subgroup on every
test scheme. Identification with the source polarization pairing is a
separate Poincare compatibility obligation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u v

variable {S : Scheme.{u}} {T W P : Over S} [GrpObj T] [IsCommMonObj T]
  [GrpObj W] [IsCommMonObj W] {I : Type v} [Fintype I]
  (p : I ⊕ I → (T ⟶ T)) [∀ i, IsMonHom (p i)]
  (horth : ∀ i j, i ≠ j → p i ≫ p j = 1)
  (hcomplete : (∏ i, p i) = 𝟙 T)
  (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := BlockGroups.Construction.fixedPointScheme (p (Sum.inl i)))
    (B := BlockGroups.Construction.fixedPointScheme (p (Sum.inr i))) (W := W))

def fullSplitSchemePairing : Annihilator.Construction.SchemeBicharacter (A := T) (B := T) (W := W) :=
  Product.Pairing.Construction.productSchemeBicharacter (PairedProjectors.Construction.pairedProjectorBlock p)
    (PairedProjectors.Construction.pairedProjectorPointEquiv p horth hcomplete)
    (PairedProjectors.Construction.pairedProjectorPointEquiv_naturality p horth hcomplete)
    (fun i => SplitPairing.Construction.splitSchemeBicharacter (e i))

def fullSplitRelativeKernel (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) P) :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup T P :=
  Product.Annihilator.Construction.decomposedRelativeSubgroup (PairedProjectors.Construction.pairedProjectorBlock p)
    (PairedProjectors.Construction.pairedProjectorPointEquiv p horth hcomplete)
    (PairedProjectors.Construction.pairedProjectorPointEquiv_naturality p horth hcomplete)
    (fun i => Relative.Isotropy.Construction.pairedRelativeSubgroup (H i) ((e i).relativeAnnihilator (H i)))

def splitKernelBlockFamily
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) P) :
    (j : I ⊕ I) → TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p j)) P
  | Sum.inl i => H i
  | Sum.inr i => (e i).relativeAnnihilator (H i)

omit [IsCommMonObj W] in
theorem mem_fullSplitRelativeKernel
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) P)
    (X : Over S) (t : X ⟶ P) (x : X ⟶ T) :
    x ∈ (fullSplitRelativeKernel p horth hcomplete e H).points X t ↔
      ∀ i, Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X x (Sum.inl i) ∈ (H i).points X t ∧
        Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X x (Sum.inr i) ∈
          ((e i).relativeAnnihilator (H i)).points X t := by
  rw [fullSplitRelativeKernel, Product.Annihilator.Construction.mem_decomposedRelativeSubgroup]
  apply forall_congr'
  intro i
  let a := Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X x (Sum.inl i)
  let b := Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X x (Sum.inr i)
  change (lift a b ≫ fst (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) (BlockGroups.Construction.fixedPointScheme (p (Sum.inr i)))
      ∈ (H i).points X t ∧
    lift a b ≫ snd (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) (BlockGroups.Construction.fixedPointScheme (p (Sum.inr i)))
      ∈ ((e i).relativeAnnihilator (H i)).points X t) ↔ _
  rw [lift_fst, lift_snd]

omit [IsCommMonObj W] in
theorem fullSplitRelativeKernel_eq_decomposed
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) P) :
    fullSplitRelativeKernel p horth hcomplete e H =
      Product.Annihilator.Construction.decomposedRelativeSubgroup (fun j => BlockGroups.Construction.fixedPointScheme (p j))
        (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete)
        (Torsion.Decomposition.Construction.schemeProjectorPointEquiv_naturality p horth hcomplete) (splitKernelBlockFamily p e H) := by
  ext X t x
  rw [mem_fullSplitRelativeKernel, Product.Annihilator.Construction.mem_decomposedRelativeSubgroup]
  constructor
  · intro h j
    cases j with
    | inl i => exact (h i).1
    | inr i => exact (h i).2
  · intro h i
    exact ⟨h (Sum.inl i), h (Sum.inr i)⟩

omit [IsCommMonObj W] in
theorem fullSplitRelativeKernel_eq_tuple
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) P)
    (s : ℕ) (r : Fin s ≃ I ⊕ I) :
    fullSplitRelativeKernel p horth hcomplete e H =
      Kernel.Tuples.Construction.tupleKernel s (fun j => SubgroupTransport.Construction.relativeSubgroupImage (BlockGroups.Construction.fixedPointInclusion (p (r j)))
        (splitKernelBlockFamily p e H (r j))) := by
  rw [fullSplitRelativeKernel_eq_decomposed]
  exact ProjectorKernel.Construction.decomposed_projector_kernel_eq_tuple p horth hcomplete _ s r

theorem fullSplitSchemePairing_alternating (X : Over S) (x : X ⟶ T) :
    (fullSplitSchemePairing p horth hcomplete e).pairValue x x = 1 := by
  rw [fullSplitSchemePairing, Product.Pairing.Construction.productSchemeBicharacter_pairValue]
  simp_rw [SplitPairing.Construction.splitSchemeBicharacter_alternating]
  exact Finset.prod_const_one

/-- The complete torsion kernel is self-annihilating for the assembled
split pairing. Every component uses the same actual torsion group T. -/
theorem fullSplitRelativeKernel_self_annihilating_of_CartierDuality
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p (Sum.inl i))) P)
    (h_CartierDuality : ∀ i, (e i).flip.relativeAnnihilator ((e i).relativeAnnihilator (H i)) = H i) :
    (fullSplitSchemePairing p horth hcomplete e).relativeAnnihilator
        (fullSplitRelativeKernel p horth hcomplete e H) =
      fullSplitRelativeKernel p horth hcomplete e H :=
  Product.Annihilator.Construction.product_relative_self_annihilating (PairedProjectors.Construction.pairedProjectorBlock p)
    (PairedProjectors.Construction.pairedProjectorPointEquiv p horth hcomplete)
    (PairedProjectors.Construction.pairedProjectorPointEquiv_naturality p horth hcomplete)
    (fun i => SplitPairing.Construction.splitSchemeBicharacter (e i))
    (fun i => Relative.Isotropy.Construction.pairedRelativeSubgroup (H i) ((e i).relativeAnnihilator (H i)))
    (fun i => SplitPairing.Construction.splitSchemeBicharacter_self_annihilating_of_CartierDuality (e i) (H i) (h_CartierDuality i))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitIsotropy.Construction
