import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Annihilator

/-! # Double Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
The proved CartierDuality double-annihilator theorem recovers the original native
subgroup on every test scheme. Both annihilations use the original
scheme pairing, including all further restrictions of a test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B H : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj H] [IsCommMonObj H]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem Annihilator.Construction.SchemeBicharacter.native_double_annihilator_from_perfect_pairing
    [IsFinite A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom]
    (i : Grp.mk H ⟶ Grp.mk A) [Mono i.hom.hom] (he : e.toSheafPairing.IsPerfect)
    (T : Over S) (x : T ⟶ A) :
    (∀ (U : Over S) (f : U ⟶ T) (y : U ⟶ B),
      (∀ (V : Over S) (g : V ⟶ U) (z : V ⟶ H), e.pairValue (z ≫ i.hom.hom) (g ≫ y) = 1) →
        e.pairValue (f ≫ x) y = 1) ↔
      ∃ z : T ⟶ H, z ≫ i.hom.hom = x := by
  have hA : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) :=
    ⟨Grp.mk A, inferInstance, inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  have hH := Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf_finiteLocallyFree i
  have hd := CartierDuality.PolarizedTorsion.annihilator_duality e.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i) he hA hH
  obtain ⟨J, hc, _hf, _hflat, _hfp, k, hk, hrep⟩ :=
    Intrinsic.SheafSubobjects.Construction.finite_sheaf_subobject_native (Grp.mk B)
      (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i)) hd.1
  let := hc
  let := hk
  have hdouble : CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.flip.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf k) = Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i := by
    rw [Annihilator.Construction.SchemeBicharacter.toSheafPairing_flip, hrep]
    exact hd.2.2.1
  have hm : (ULift.up x ∈ Sheaf.KernelSections.Construction.sheafSubobjectSections T
      (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.flip.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf k))) ↔
      ULift.up x ∈ Sheaf.KernelSections.Construction.sheafSubobjectSections T (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i) := by rw [hdouble]
  rw [e.flip.toSheafPairing_annihilator_sections k, Sheaf.AnnihilatorSections.Construction.mem_nativeSubgroupSheaf_sections i] at hm
  apply Iff.trans ?_ hm
  constructor
  · intro h U f z
    rw [Annihilator.Construction.SchemeBicharacter.flip_pairValue]
    apply h U f (z ≫ k.hom.hom)
    apply (e.toSheafPairing_annihilator_sections i U (z ≫ k.hom.hom)).mp
    rw [← hrep]
    exact (Sheaf.AnnihilatorSections.Construction.mem_nativeSubgroupSheaf_sections k U _).mpr ⟨z, rfl⟩
  · intro h U f y hy
    have hm' : ULift.up y ∈ Sheaf.KernelSections.Construction.sheafSubobjectSections U (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf k) := by
      rw [hrep]
      exact (e.toSheafPairing_annihilator_sections i U y).mpr hy
    obtain ⟨z, rfl⟩ := (Sheaf.AnnihilatorSections.Construction.mem_nativeSubgroupSheaf_sections k U y).mp hm'
    simpa only [Annihilator.Construction.SchemeBicharacter.flip_pairValue] using h U f z

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
