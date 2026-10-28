import OAI.ArithmeticGeometry.Models.GluingBaseChange
import OAI.ArithmeticGeometry.Models.ModelFiniteness

/-! # Gluing Finiteness -/

namespace OAI.ArithmeticGeometry.Models.GluingFiniteness.Constructions.Foundations

/-! Finiteness of a binary gluing over a noetherian affine base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem openGluedOver_finitePresentation {S : Scheme.{u}}
    [IsAffine S] [IsLocallyNoetherian S]
    {W X Y : Over S} (f : W ⟶ X) (g : W ⟶ Y)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left]
    (hX : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom) :
    Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (GluingBaseChange.Constructions.Foundations.openGluedOver f g).hom := by
  let P := GluingBaseChange.Constructions.Foundations.openGluedOver f g
  let i := GluingBaseChange.Constructions.Foundations.openGluedInl f g
  let j := GluingBaseChange.Constructions.Foundations.openGluedInr f g
  let : IsOpenImmersion i.left := OpenPushout.Constructions.Foundations.openPushout_inl_open f.left g.left
  let : IsOpenImmersion j.left := OpenPushout.Constructions.Foundations.openPushout_inr_open f.left g.left
  let C := OpenPushout.Constructions.Foundations.openPairCover i.left j.left (OpenPushout.Constructions.Foundations.openPushout_covers f.left g.left)
  let : LocallyOfFinitePresentation X.hom := hX.1
  let : LocallyOfFinitePresentation Y.hom := hY.1
  let : QuasiCompact X.hom := hX.2.1
  let : QuasiCompact Y.hom := hY.2.1
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : ∀ k, CompactSpace (C.X k) := fun k ↦ by cases k <;> assumption
  let : Finite C.I₀ := inferInstanceAs (Finite Bool)
  let : CompactSpace P.left := C.compactSpace
  let : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  let : LocallyOfFinitePresentation P.hom := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation.{u}) C).mpr
    intro k
    cases k
    · change LocallyOfFinitePresentation (i.left ≫ P.hom)
      rw [i.w]
      infer_instance
    · change LocallyOfFinitePresentation (j.left ≫ P.hom)
      rw [j.w]
      infer_instance
  let : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  let : IsNoetherian P.left := ⟨⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end OAI.ArithmeticGeometry.Models.GluingFiniteness.Constructions.Foundations
