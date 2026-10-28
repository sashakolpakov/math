import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingIsoAnnihilator

/-! # Opposite Block Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeBlockTransport

noncomputable section

/-! Ambient annihilator images are unchanged by the constructed
isomorphisms between native coefficient blocks, provided their original
ambient inclusions commute. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B C U V W P : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj U] [GrpObj V] [GrpObj W]

theorem pullback_comp_square (a : U ≅ B) [IsMonHom a.hom]
    (i : B ⟶ A) (j : U ⟶ A) [IsMonHom i] [IsMonHom j]
    (ha : a.hom ≫ i = j) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback a.hom (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback i F) =
      AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback j F := by
  ext T t x
  change (x ≫ a.hom) ≫ i ∈ F.points T t ↔ x ≫ j ∈ F.points T t
  rw [Category.assoc, ha]

theorem image_pullback_iso_square (b : V ≅ C) [IsMonHom b.hom]
    (i : C ⟶ A) (j : V ⟶ A) [IsMonHom i] [IsMonHom j]
    (hb : b.hom ≫ i = j) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup C P) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage j (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback b.hom F) = AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage i F := by
  ext T t x
  change (∃ v, v ≫ b.hom ∈ F.points T t ∧ v ≫ j = x) ↔
    ∃ c, c ∈ F.points T t ∧ c ≫ i = x
  constructor
  · rintro ⟨v, hv, hx⟩
    refine ⟨v ≫ b.hom, hv, ?_⟩
    rw [Category.assoc, hb]
    exact hx
  · rintro ⟨c, hc, hx⟩
    refine ⟨c ≫ b.inv, ?_, ?_⟩
    · simpa only [Category.assoc, b.inv_hom_id, Category.comp_id] using hc
    · rw [Category.assoc, ← hb, b.inv_hom_id_assoc]
      exact hx

theorem opposite_image_block_iso
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := B) (B := C) (W := W))
    (a : U ≅ B) (b : V ≅ C) [IsMonHom a.hom] [IsMonHom b.hom]
    (i : B ⟶ A) (j : U ⟶ A) (k : C ⟶ A) (l : V ⟶ A)
    [IsMonHom i] [IsMonHom j] [IsMonHom k] [IsMonHom l]
    (ha : a.hom ≫ i = j) (hb : b.hom ≫ k = l) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage l ((e.restrict a.hom b.hom).relativeAnnihilator
      (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback j F)) =
        AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage k (e.relativeAnnihilator (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback i F)) := by
  rw [← pullback_comp_square a i j ha F, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_annihilator_iso,
    image_pullback_iso_square b k l hb]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeBlockTransport
