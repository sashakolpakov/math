import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactKernelRecovery
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy

/-! # Compact Opposites -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactOpposites.Kernel

noncomputable section

/-!
Compute the compact opposite kernels in the actual multiplier-level
pairing. The annihilator of zero is the whole opposite block; CartierDuality's
double-annihilator clause makes the annihilator of the whole block zero.
The level remains n=q^i throughout.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

variable {S : Scheme.{u}} {A B P : Over S} [GrpObj A] [GrpObj B]

def wholeRelativeSubgroup (A P : Over S) [GrpObj A] : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P where
  points _ _ := ⊤
  naturality := by intros; trivial

theorem pullback_fixed_whole (i : B ⟶ A) [IsMonHom i] :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback i (Kernel.Base.fixedKernelFamily (P := P) i) = wholeRelativeSubgroup B P := by
  ext T t x
  change (∃ y : T ⟶ B, y ≫ i = x ≫ i) ↔ True
  exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩

variable [IsCommMonObj A] [IsCommMonObj B]

theorem pullback_trivial (i : B ⟶ A) [IsMonHom i] [Mono i] :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback i (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (P := P)) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := P) := by
  ext T t x
  change x ≫ i = 1 ↔ x = 1
  constructor
  · intro h
    apply (cancel_mono i).mp
    exact h.trans (MonObj.one_comp i).symm
  · rintro rfl
    exact MonObj.one_comp i

omit [IsCommMonObj A] [IsCommMonObj B] in
theorem image_whole_fixed (i : B ⟶ A) [IsMonHom i] :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage i (wholeRelativeSubgroup B P) = Kernel.Base.fixedKernelFamily (P := P) i := by
  ext T t x
  change (∃ y : T ⟶ B, y ∈ (⊤ : Subgroup (T ⟶ B)) ∧ y ≫ i = x) ↔
    ∃ y : T ⟶ B, y ≫ i = x
  simp only [Subgroup.mem_top, true_and]

theorem image_trivial (i : B ⟶ A) [IsMonHom i] :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage i (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := P)) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := A) (P := P) := by
  ext T t x
  change (∃ y : T ⟶ B, y = 1 ∧ y ≫ i = x) ↔ x = 1
  simp only [exists_eq_left, MonObj.one_comp, eq_comm]

variable {W : Over S} [GrpObj W]
variable (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))

omit [IsCommMonObj B] in
theorem annihilator_trivial :
    e.relativeAnnihilator (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := A) (P := P)) =
      wholeRelativeSubgroup B P := by
  ext T t y
  constructor
  · intro _; trivial
  · intro _ U f x hx
    change x = 1 at hx
    rw [hx]
    exact e.one_left U _

omit [IsCommMonObj A] in
/-- The input is the exact CartierDuality double-annihilator clause at the zero
subgroup, independent of every quotient and operator in NeighborCounting. -/
theorem annihilator_whole_of_CartierDuality
    (hCartierDuality : e.relativeAnnihilator
      (e.flip.relativeAnnihilator (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := P))) =
        AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := P)) :
    e.relativeAnnihilator (wholeRelativeSubgroup A P) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := B) (P := P) := by
  rw [annihilator_trivial e.flip] at hCartierDuality
  exact hCartierDuality

variable (n : ℕ) (p r : A ⟶ A) [IsMonHom p] [IsMonHom r]
variable (pairing : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
  (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r) (W := W))

/-- The opposite of an empty compact chosen kernel is the complete
opposite n-torsion block, even in characteristic q. -/
theorem opposite_of_trivial :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p r pairing (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := A) (P := P)) =
      Kernel.Base.fixedKernelFamily (P := P) (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n r) := by
  rw [AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel, pullback_trivial, annihilator_trivial, image_whole_fixed]

/-- The opposite of a whole compact chosen n-torsion kernel is trivial.
The pairing remains the actual pairing at multiplier level n. -/
theorem opposite_of_whole
    (hCartierDuality : pairing.relativeAnnihilator
      (pairing.flip.relativeAnnihilator
        (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r) (P := P))) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r) (P := P)) :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n p r pairing (Kernel.Base.fixedKernelFamily (P := P) (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p)) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := A) (P := P) := by
  rw [AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel, pullback_fixed_whole, annihilator_whole_of_CartierDuality pairing hCartierDuality, image_trivial]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactOpposites.Kernel
