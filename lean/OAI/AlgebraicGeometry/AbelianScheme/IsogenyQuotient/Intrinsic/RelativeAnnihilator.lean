import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.DoubleAnnihilator

/-! # Relative Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
Translate CartierDuality's native double-annihilator theorem to the relative
subgroup functor used by the quotient construction. The subgroup is the
original native image and both annihilators use the actual scheme map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

def Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup {S : Scheme.{u}} {A H : Over S}
    [GrpObj A] [GrpObj H] (i : H ⟶ A) [IsMonHom i] :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup A (Over.mk (𝟙 S)) where
  points T _ := (IsMonHom.monoidHom i T).range
  naturality := by
    intro X Y f t a ha
    obtain ⟨x, rfl⟩ := ha
    exact ⟨f ≫ x, Category.assoc f x i⟩

def Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup_model {S : Scheme.{u}} {A H : Over S}
    [GrpObj A] [GrpObj H] (i : H ⟶ A) [IsMonHom i] [Mono i]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom] :
    (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i).Model where
  carrier := H
  toBase := Over.homMk H.hom (Category.comp_id _)
  toGroup := i
  finite := inferInstanceAs (IsFinite H.hom)
  flat := inferInstanceAs (Flat H.hom)
  finitePresentation := inferInstanceAs (LocallyOfFinitePresentation H.hom)
  jointly_monic _ _ _ _ hh := (cancel_mono i).mp hh
  points_iff X t a := by
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨h, ?_, hh⟩
      apply Over.OverMorphism.ext
      exact h.w.trans (t.w.symm.trans (Category.comp_id t.left))
    · rintro ⟨h, _, hh⟩
      exact ⟨h, hh⟩

variable {S : Scheme.{u}} {A B H : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj H] [IsCommMonObj H]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

omit [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj H] in
theorem Annihilator.Construction.SchemeBicharacter.nativeImage_annihilator_membership (i : H ⟶ A) [IsMonHom i]
    (T : Over S) (t : T ⟶ Over.mk (𝟙 S)) (y : T ⟶ B) :
    y ∈ (e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i)).points T t ↔
      ∀ (U : Over S) (f : U ⟶ T) (x : U ⟶ H), e.pairValue (x ≫ i) (f ≫ y) = 1 := by
  constructor
  · intro h U f x
    exact h U f (x ≫ i) ⟨x, rfl⟩
  · intro h U f x hx
    obtain ⟨z, rfl⟩ := hx
    exact h U f z

theorem Annihilator.Construction.SchemeBicharacter.nativeImage_relative_double_annihilator
    [IsFinite A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom]
    (i : Grp.mk H ⟶ Grp.mk A) [Mono i.hom.hom] (he : e.toSheafPairing.IsPerfect) :
    e.flip.relativeAnnihilator (e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom)) =
      Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom := by
  ext T t x
  change (∀ (U : Over S) (f : U ⟶ T) (y : U ⟶ B),
    y ∈ (e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom)).points U (f ≫ t) →
      e.flip.pairValue y (f ≫ x) = 1) ↔ _
  simp only [Annihilator.Construction.SchemeBicharacter.nativeImage_annihilator_membership, Annihilator.Construction.SchemeBicharacter.flip_pairValue]
  exact e.native_double_annihilator_from_perfect_pairing i he T x

theorem Annihilator.Construction.SchemeBicharacter.nativeImage_relative_annihilator_has_model
    [IsFinite A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom]
    (i : Grp.mk H ⟶ Grp.mk A) [Mono i.hom.hom] (he : e.toSheafPairing.IsPerfect) :
    Nonempty (e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom)).Model := by
  obtain ⟨J, hc, k, hf, hflat, hfp, hk, hpoints⟩ := e.native_annihilator_from_perfect_pairing i he
  let := hc
  let := hf
  let := hflat
  let := hfp
  let := hk
  have heq : e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom) =
      Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup k.hom.hom := by
    ext T t y
    rw [Annihilator.Construction.SchemeBicharacter.nativeImage_annihilator_membership]
    exact (hpoints T y).symm
  rw [heq]
  exact ⟨Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup_model k.hom.hom⟩

theorem Annihilator.Construction.SchemeBicharacter.nativeImage_relative_annihilator_model_and_double
    [IsFinite A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom]
    (i : Grp.mk H ⟶ Grp.mk A) [Mono i.hom.hom] (he : e.toSheafPairing.IsPerfect) :
    Nonempty (e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom)).Model ∧
      e.flip.relativeAnnihilator (e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom)) =
        Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom :=
  ⟨e.nativeImage_relative_annihilator_has_model i he,
    e.nativeImage_relative_double_annihilator i he⟩

theorem Annihilator.Construction.SchemeBicharacter.commGroupImage_relative_annihilator_model_and_double
    [IsFinite A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    (J : CommGrp (Over S))
    [IsFinite J.X.hom] [Flat J.X.hom] [LocallyOfFinitePresentation J.X.hom]
    (i : J.toGrp ⟶ Grp.mk A) [Mono i.hom.hom] (he : e.toSheafPairing.IsPerfect) :
    Nonempty (e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom)).Model ∧
      e.flip.relativeAnnihilator (e.relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom)) =
        Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i.hom.hom :=
  e.nativeImage_relative_annihilator_model_and_double i he

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
