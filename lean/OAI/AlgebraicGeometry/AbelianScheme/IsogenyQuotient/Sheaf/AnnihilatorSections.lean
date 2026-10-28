import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.AnnihilatorKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.KernelSections

/-! # Annihilator Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
The canonical CartierDuality annihilator has precisely the original scheme-valued
annihilator sections. The same statement for native subgroup inclusions
retains their original ranges, independent of a subobject representative.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem Sheaf.AnnihilatorSections.Construction.mem_nativeSubgroupSheaf_sections {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (i : H ⟶ G) [Mono i.hom.hom]
    (T : Over S) (x : T ⟶ G.X) :
    ULift.up x ∈ Sheaf.KernelSections.Construction.sheafSubobjectSections T (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i) ↔
      ∃ y : T ⟶ H.X, y ≫ i.hom.hom = x := by
  have := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono i
  change ULift.up x ∈ Sheaf.KernelSections.Construction.sheafSubobjectSections T (Subobject.mk (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)) ↔ _
  rw [Sheaf.KernelSections.Construction.sheafSubobjectSections_mk]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.down, congrArg ULift.down hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨ULift.up y, congrArg ULift.up hy⟩

variable {S : Scheme.{u}} {A B H : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj H] [IsCommMonObj H]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_annihilator_sections (i : Grp.mk H ⟶ Grp.mk A) [Mono i.hom.hom]
    (T : Over S) (y : T ⟶ B) :
    ULift.up y ∈ Sheaf.KernelSections.Construction.sheafSubobjectSections T
        (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i)) ↔
      ∀ (U : Over S) (f : U ⟶ T) (x : U ⟶ H),
        e.pairValue (x ≫ i.hom.hom) (f ≫ y) = 1 := by
  rw [Annihilator.Construction.SchemeBicharacter.toSheafPairing_annihilator_kernel, Sheaf.KernelSections.Construction.sheafSubobjectSections_kernel]
  change e.rightRestrictionCharacter i.hom.hom T y = 1 ↔ _
  exact e.rightRestrictionCharacter_eq_one_iff i.hom.hom T y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
