import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseChange
import Mathlib.RingTheory.RingHom.FinitePresentation

/-! # Finite Presentation -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePresentation.Construction

noncomputable section

section

/-! Finite presentation of the multiplication map in the Openness proof. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- If a composite is locally finitely presented and its second morphism
is locally of finite type, then the first morphism is locally finitely presented. -/
theorem locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFinitePresentation) (Q := @RingHom.FinitePresentation)
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFinitePresentation) (Q := @RingHom.FinitePresentation)
  have : MorphismProperty.RespectsRight
      (@LocallyOfFinitePresentation : MorphismProperty Scheme) @IsOpenImmersion :=
    { postcomp := fun i hi h hh => by
        have := hi
        have := hh
        infer_instance }
  apply IsZariskiLocalAtSource.iff_exists_resLE.mpr
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((f ≫ g) x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxW (W.isOpen.preimage g.continuous)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.isOpen.preimage f.continuous)
  change IsAffineOpen W at hW
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  change U ≤ g ⁻¹ᵁ W at hUW
  change V ≤ f ⁻¹ᵁ U at hVU
  let hVW : V ≤ (f ≫ g) ⁻¹ᵁ W := fun y hy => hUW (hVU hy)
  have hfp := (f ≫ g).finitePresentation_appLE hW hV hVW
  have hft := g.finiteType_appLE hW hU hUW
  have hcomp :
      ((f.appLE U V hVU).hom.comp (g.appLE W U hUW).hom).FinitePresentation := by
    rw [← CommRingCat.hom_comp, f.appLE_comp_appLE g W U V hUW hVU]
    exact hfp
  have hlocal : (f.appLE U V hVU).hom.FinitePresentation :=
    RingHom.FinitePresentation.of_comp_finiteType _ hcomp hft
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine (U : Scheme) := hU
  have : IsAffine (V : Scheme) := hV
  apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr
  exact (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr hlocal

/-- Every endomorphism of an S-scheme locally of finite presentation is
locally of finite presentation over that S-scheme. -/
theorem locallyOfFinitePresentation_overEnd
    {S : Scheme} (A : Over S) [LocallyOfFinitePresentation A.hom] (f : A ⟶ A) :
    LocallyOfFinitePresentation f.left := by
  have : LocallyOfFinitePresentation (f.left ≫ A.hom) := by
    rw [f.w]
    infer_instance
  exact locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType f.left A.hom

/-- Multiplication on a smooth group scheme is locally finitely presented. -/
theorem locallyOfFinitePresentation_multiplication
    {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] (n : ℕ) :
    LocallyOfFinitePresentation (Multiplication.Construction.multiplicationMap A n).left :=
  locallyOfFinitePresentation_overEnd A (Multiplication.Construction.multiplicationMap A n)

end

/-! The torsion kernel as a pullback of multiplication along the identity section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]

/-- The scheme-theoretic torsion kernel is the pullback over the identity. -/
theorem torsion_isPullback_over (n : ℕ) :
    IsPullback (DefinitionsTorsion.Construction.torsionInclusion A n) (toUnit (DefinitionsTorsion.Construction.torsionScheme A n))
      (Multiplication.Construction.multiplicationMap A n) η[A] := by
  have hcomm : DefinitionsTorsion.Construction.torsionInclusion A n ≫ Multiplication.Construction.multiplicationMap A n =
      toUnit (DefinitionsTorsion.Construction.torsionScheme A n) ≫ η[A] := by
    have h := equalizer.condition ((𝟙 A) ^ n) (1 : A ⟶ A)
    simpa only [DefinitionsTorsion.Construction.torsionInclusion, DefinitionsTorsion.Construction.torsionScheme, Multiplication.Construction.multiplicationMap,
      Hom.one_def, comp_toUnit_assoc] using h
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk (DefinitionsTorsion.Construction.torsionInclusion A n) (toUnit (DefinitionsTorsion.Construction.torsionScheme A n)) hcomm)
  apply PullbackCone.IsLimit.mk hcomm
    (fun c => equalizer.lift c.fst (by
      change c.fst ≫ Multiplication.Construction.multiplicationMap A n = c.fst ≫ (1 : A ⟶ A)
      rw [c.condition, MonObj.comp_one]
      change c.snd ≫ η[A] = toUnit c.pt ≫ η[A]
      rw [toUnit_unique c.snd (toUnit c.pt)]))
  · intro c
    exact equalizer.lift_ι _ _
  · intro c
    exact toUnit_unique _ _
  · intro c m hfst hsnd
    apply equalizer.hom_ext
    exact hfst.trans (equalizer.lift_ι _ _).symm

/-- The underlying square is a pullback in schemes. -/
theorem torsion_isPullback (n : ℕ) :
    IsPullback (DefinitionsTorsion.Construction.torsionInclusion A n).left (DefinitionsTorsion.Construction.torsionScheme A n).hom
      (Multiplication.Construction.multiplicationMap A n).left η[A].left := by
  have h := (torsion_isPullback_over A n).map (Over.forget S)
  change IsPullback (DefinitionsTorsion.Construction.torsionInclusion A n).left (toUnit (DefinitionsTorsion.Construction.torsionScheme A n)).left
    (Multiplication.Construction.multiplicationMap A n).left η[A].left at h
  simpa only [Over.toUnit_left] using h

/-- The torsion scheme of a smooth group scheme is locally finitely presented. -/
theorem locallyOfFinitePresentation_torsion [Smooth A.hom] (n : ℕ) :
    LocallyOfFinitePresentation (DefinitionsTorsion.Construction.torsionScheme A n).hom := by
  exact MorphismProperty.of_isPullback (torsion_isPullback A n)
    (locallyOfFinitePresentation_multiplication A n)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePresentation.Construction
