import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Schematic Closure -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SchematicClosure.Construction

noncomputable section

/-! Schematic closure of a closed subscheme along a quasi-compact preimmersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem preimmersion_toImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] :
    IsPreimmersion f.toImage := by
  have : IsPreimmersion (f.toImage ≫ f.imageι) := by
    rw [f.toImage_imageι]
    infer_instance
  exact IsPreimmersion.of_comp f.toImage f.imageι

/-- A preimmersion induces injective maps on stalks after replacing its
target by its schematic image. -/
theorem preimmersion_toImage_stalkMap_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] [QuasiCompact f] (x : X) :
    Function.Injective (f.toImage.stalkMap x) := by
  have : IsPreimmersion f.toImage := preimmersion_toImage f
  have : IsIso (X.presheaf.stalkPushforward CommRingCat f.toImage.base x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      CommRingCat f.toImage.isEmbedding.isInducing X.presheaf x
  change Function.Injective
    (((TopCat.Presheaf.stalkFunctor CommRingCat (f.toImage x)).map f.toImage.c) ≫
      X.presheaf.stalkPushforward CommRingCat f.toImage.base x)
  exact (ConcreteCategory.bijective_of_isIso
      (X.presheaf.stalkPushforward CommRingCat f.toImage.base x)).1.comp
    (f.stalkFunctor_toImage_injective (f.toImage x))

def closurePullbackLift
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z) :
    X ⟶ pullback j (i ≫ j).imageι :=
  pullback.lift i (i ≫ j).toImage (i ≫ j).toImage_imageι.symm

@[reassoc (attr := simp)]
theorem closurePullbackLift_fst
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z) :
    closurePullbackLift i j ≫ pullback.fst j (i ≫ j).imageι = i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem closurePullbackLift_snd
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z) :
    closurePullbackLift i j ≫ pullback.snd j (i ≫ j).imageι = (i ≫ j).toImage :=
  pullback.lift_snd _ _ _

/-- A closed subscheme of a quasi-compact preimmersed scheme is recovered by
pulling its schematic closure back along that preimmersion. In particular,
this applies to the inclusion of a generic fiber. -/
theorem closurePullbackLift_isIso
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsPreimmersion j] [QuasiCompact (i ≫ j)] :
    IsIso (closurePullbackLift i j) := by
  let f := i ≫ j
  let a := pullback.fst j f.imageι
  let b := pullback.snd j f.imageι
  let l := closurePullbackLift i j
  have hla : l ≫ a = i := closurePullbackLift_fst i j
  have hlb : l ≫ b = f.toImage := closurePullbackLift_snd i j
  have : IsClosedImmersion (l ≫ a) := by rw [hla]; infer_instance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp_isClosedImmersion l a
  have hrange : Set.range a = Set.range i := by
    change Set.range (pullback.fst j f.imageι) = Set.range i
    rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker]
    change j ⁻¹' closure (Set.range (i ≫ j)) = Set.range i
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      ← j.isEmbedding.closure_eq_preimage_closure_image]
    exact i.isClosedEmbedding.isClosed_range.closure_eq
  have : Surjective l := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hrange ▸ (Set.mem_range_self y : a y ∈ Set.range a)
    refine ⟨x, a.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hla]
    exact hx
  apply isIso_iff_isIso_stalkMap l |>.mpr
  constructor
  · exact inferInstanceAs (IsIso (TopCat.isoOfHomeo
      (l.isEmbedding.toHomeomorphOfSurjective l.surjective)).hom)
  · intro x
    have hinj : Function.Injective ((l ≫ b).stalkMap x) := by
      exact (congrArg (fun h : X ⟶ f.image => Function.Injective (h.stalkMap x))
        hlb).mpr (preimmersion_toImage_stalkMap_injective f x)
    rw [Scheme.Hom.stalkMap_comp] at hinj
    have hinjl : Function.Injective (l.stalkMap x) := by
      intro r s hrs
      obtain ⟨r', rfl⟩ := b.stalkMap_surjective (l x) r
      obtain ⟨s', rfl⟩ := b.stalkMap_surjective (l x) s
      exact congrArg (b.stalkMap (l x)) (hinj hrs)
    exact (ConcreteCategory.isIso_iff_bijective (l.stalkMap x)).mpr
      ⟨hinjl, l.stalkMap_surjective x⟩

/-- The schematic image square along a preimmersion is cartesian. -/
theorem schematicClosure_isPullback
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsPreimmersion j] [QuasiCompact (i ≫ j)] :
    IsPullback i (i ≫ j).toImage j (i ≫ j).imageι := by
  have : IsIso (closurePullbackLift i j) := closurePullbackLift_isIso i j
  exact IsPullback.of_iso_pullback ⟨(i ≫ j).toImage_imageι.symm⟩
    (asIso (closurePullbackLift i j))
    (closurePullbackLift_fst i j) (closurePullbackLift_snd i j)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SchematicClosure.Construction
