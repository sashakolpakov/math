import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

/-! # Family Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport.Family

noncomputable section

/-! Image families retain their actual embedded subgroups under native
composition and isomorphisms of models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

variable {S : Scheme.{u}} {A B H G P : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj H] [GrpObj G]

theorem image_fixed (i : H ⟶ B) (j : B ⟶ A) [IsMonHom i] [IsMonHom j] :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage j (Base.fixedKernelFamily (P := P) i) = Base.fixedKernelFamily (P := P) (i ≫ j) := by
  ext T t a
  change (∃ b, (∃ h, h ≫ i = b) ∧ b ≫ j = a) ↔ ∃ h, h ≫ (i ≫ j) = a
  constructor
  · rintro ⟨b, ⟨h, rfl⟩, ha⟩
    exact ⟨h, (Category.assoc _ _ _).symm.trans ha⟩
  · rintro ⟨h, ha⟩
    exact ⟨h ≫ i, ⟨h, rfl⟩, (Category.assoc _ _ _).trans ha⟩

theorem pullback_fixed_comp (i : H ⟶ B) (j : B ⟶ A)
    [IsMonHom i] [IsMonHom j] [Mono j] :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback j (Base.fixedKernelFamily (P := P) (i ≫ j)) =
      Base.fixedKernelFamily (P := P) i := by
  ext T t b
  change (∃ h, h ≫ (i ≫ j) = b ≫ j) ↔ ∃ h, h ≫ i = b
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, (cancel_mono j).mp ((Category.assoc _ _ _).trans hh)⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, (Category.assoc _ _ _).symm⟩

theorem fixed_iso (i : H ⟶ A) (j : G ⟶ A) [IsMonHom i] [IsMonHom j]
    (e : H ≅ G) (he : e.hom ≫ j = i) :
    Base.fixedKernelFamily (P := P) i = Base.fixedKernelFamily (P := P) j := by
  ext T t a
  change (∃ h, h ≫ i = a) ↔ ∃ g, g ≫ j = a
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h ≫ e.hom, by rw [Category.assoc, he]⟩
  · rintro ⟨g, rfl⟩
    refine ⟨g ≫ e.inv, ?_⟩
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport.Family
