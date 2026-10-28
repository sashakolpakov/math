import OAI.ArithmeticGeometry.Models.SpreadingOut.SchematicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Image -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Image.Construction

noncomputable section

/-! Reduced schematic images and factorizations through closed subschemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem schematic_image_reduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] : IsReduced f.image := by
  have hred (U : Y.affineOpens) :
      _root_.IsReduced (Γ(Y, U) ⧸ f.ker.ideal U) := by
    rw [f.ker_apply]
    have : _root_.IsReduced (f.app U.1).hom.range :=
      isReduced_of_injective _ (f.app U.1).hom.range.subtype_injective
    exact isReduced_of_injective (RingHom.quotientKerEquivRange (f.app U.1).hom).toRingHom
      (RingHom.quotientKerEquivRange (f.app U.1).hom).injective
  have (U : f.ker.subschemeCover.openCover.I₀) :
      IsReduced (f.ker.subschemeCover.openCover.X U) := by
    let V : Y.affineOpens := U
    have := hred V
    change IsReduced (Spec (.of (Γ(Y, V.1) ⧸ f.ker.ideal V)))
    infer_instance
  exact IsReduced.of_openCover f.image f.ker.subschemeCover.openCover

/-- A map from a reduced scheme whose image lies in a closed subscheme
factors uniquely through that closed subscheme. -/
theorem reduced_factors_through_closed_immersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (i : Y ⟶ Z)
    [IsReduced X] [IsClosedImmersion i]
    (h : Set.range f ⊆ Set.range i) :
    ∃ l : X ⟶ Y, l ≫ i = f := by
  have hs : Surjective (pullback.snd i f) := by
    rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun x ↦ h (Set.mem_range_self x)
  have := hs
  have : IsIso (pullback.snd i f) :=
    isIso_of_isClosedImmersion_of_surjective (pullback.snd i f)
  refine ⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- The schematic closure of an immersion of a reduced scheme contains the
original scheme as a dense open subscheme and is itself reduced. -/
theorem reduced_immersion_image
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [QuasiCompact f] [IsReduced X] :
    IsReduced f.image ∧ IsOpenImmersion f.toImage ∧ IsDominant f.toImage :=
  ⟨schematic_image_reduced f, inferInstance, inferInstance⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Image.Construction
