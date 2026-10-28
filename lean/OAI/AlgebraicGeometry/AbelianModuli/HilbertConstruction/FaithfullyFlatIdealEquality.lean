import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Faithfully Flat Ideal Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatIdealEquality

noncomputable section

/-! Faithfully flat quasi-compact pullback detects equality of actual ideal sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A pulled-back ideal vanishes precisely when the morphism factors through its closed subscheme. -/
theorem ideal_comap_eq_bot_iff_le_ker (I : X.IdealSheafData) (f : Y ⟶ X) :
    I.comap f = ⊥ ↔ I ≤ f.ker := by
  rw [eq_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot]

/-- A faithfully flat quasi-compact base change detects the zero ideal. -/
theorem ideal_eq_bot_of_faithfullyFlat (f : Y ⟶ X) [Flat f] [Surjective f] [QuasiCompact f]
    (I : X.IdealSheafData) (h : I.comap f = ⊥) : I = ⊥ := by
  have hfst : IsIso (pullback.fst f I.subschemeι) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr h
  have : IsIso I.subschemeι :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := f) (g := I.subschemeι) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfst
  exact I.ker_subschemeι.symm.trans I.subschemeι.ker_eq_bot_of_isIso

/-- Inclusion of ideals can be checked after faithfully flat quasi-compact base change. -/
theorem ideal_le_of_faithfullyFlat (f : Y ⟶ X) [Flat f] [Surjective f] [QuasiCompact f]
    (I J : X.IdealSheafData) (h : I.comap f ≤ J.comap f) : I ≤ J := by
  let p := pullback.fst f J.subschemeι
  let q := pullback.snd f J.subschemeι
  have hp : (I.comap f).comap p = ⊥ :=
    (ideal_comap_eq_bot_iff_le_ker (I.comap f) p).mpr h
  have hz : (I.comap J.subschemeι).comap q = ⊥ :=
    (I.comap_comp q J.subschemeι).symm.trans
      ((congrArg (fun a => I.comap a) (pullback.condition (f := f) (g := J.subschemeι)).symm).trans
        ((I.comap_comp p f).trans hp))
  have : Flat q := inferInstanceAs (Flat (pullback.snd f J.subschemeι))
  have : Surjective q := inferInstanceAs (Surjective (pullback.snd f J.subschemeι))
  have : QuasiCompact q := inferInstanceAs (QuasiCompact (pullback.snd f J.subschemeι))
  have hzero : I.comap J.subschemeι = ⊥ := ideal_eq_bot_of_faithfullyFlat q _ hz
  exact ((ideal_comap_eq_bot_iff_le_ker I J.subschemeι).mp hzero).trans_eq J.ker_subschemeι

/-- Ideal sheaves are distinguished by faithfully flat quasi-compact pullback. -/
theorem ideal_comap_injective_of_faithfullyFlat (f : Y ⟶ X) [Flat f] [Surjective f] [QuasiCompact f] :
    Function.Injective (fun I : X.IdealSheafData => I.comap f) := by
  intro I J h
  exact le_antisymm (ideal_le_of_faithfullyFlat f I J h.le)
    (ideal_le_of_faithfullyFlat f J I h.ge)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatIdealEquality
