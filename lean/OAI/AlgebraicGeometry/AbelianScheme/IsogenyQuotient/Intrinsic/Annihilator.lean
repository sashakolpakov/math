import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.SheafSubobjects
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
Apply the proved CartierDuality annihilator theorem to the actual scheme pairing.
The resulting native finite locally free subgroup has exactly the
original all-test annihilator sections, over an arbitrary base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B H : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj H] [IsCommMonObj H]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem Annihilator.Construction.SchemeBicharacter.native_annihilator_from_perfect_pairing
    [IsFinite A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom]
    (i : Grp.mk H ⟶ Grp.mk A) [Mono i.hom.hom] (he : e.toSheafPairing.IsPerfect) :
    ∃ (J : Grp (Over S)) (hc : IsCommMonObj J.X),
      letI := hc
      ∃ k : J ⟶ Grp.mk B,
        IsFinite J.X.hom ∧ Flat J.X.hom ∧ LocallyOfFinitePresentation J.X.hom ∧ Mono k.hom.hom ∧
        ∀ (T : Over S) (y : T ⟶ B),
          (∃ z : T ⟶ J.X, z ≫ k.hom.hom = y) ↔
            ∀ (U : Over S) (f : U ⟶ T) (x : U ⟶ H),
              e.pairValue (x ≫ i.hom.hom) (f ≫ y) = 1 := by
  have hA : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) :=
    ⟨Grp.mk A, inferInstance, inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  have hH := Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf_finiteLocallyFree i
  have hJ := (CartierDuality.PolarizedTorsion.annihilator_duality e.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i) he hA hH).1
  obtain ⟨J, hc, hf, hflat, hfp, k, hk, hrep⟩ :=
    Intrinsic.SheafSubobjects.Construction.finite_sheaf_subobject_native (Grp.mk B) (CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e.toSheafPairing (Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i)) hJ
  let := hc
  let := hk
  refine ⟨J, hc, k, hf, hflat, hfp, hk, ?_⟩
  intro T y
  rw [← Sheaf.AnnihilatorSections.Construction.mem_nativeSubgroupSheaf_sections k T y, hrep]
  exact e.toSheafPairing_annihilator_sections i T y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
