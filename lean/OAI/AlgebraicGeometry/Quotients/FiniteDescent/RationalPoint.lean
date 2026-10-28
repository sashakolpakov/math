import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Spec

/-! # Rational Point -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalPoint

noncomputable section

/-! A rational point over a field has that field as its residue field.
The statement is expressed through its canonical factorization. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.RationalPointResidue

variable {K : Type u} [Field K] {S : Scheme.{u}}
variable (t : S ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ S) (hs : s ≫ t = 𝟙 _)

abbrev point := s (IsLocalRing.closedPoint K)

abbrev fieldMap : S.residueField (point s) ⟶ .of K :=
  Scheme.descResidueField (Scheme.stalkClosedPointTo s)

theorem factor : Spec.map (fieldMap s) ≫ S.fromSpecResidueField (point s) = s :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S s

include hs

theorem isIso_fieldMap : IsIso (fieldMap s) := by
  let a := fieldMap s
  have : Mono a := ConcreteCategory.mono_of_injective a a.hom.injective
  obtain ⟨b, hb⟩ := Spec.map_surjective (S.fromSpecResidueField (point s) ≫ t)
  have he : Spec.map a ≫ Spec.map b = 𝟙 (Spec (.of K)) := by
    rw [hb, ← Category.assoc, factor, hs]
  have hba : b ≫ a = 𝟙 (CommRingCat.of K) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id] using he
  let e : S.residueField (point s) ≅ .of K :=
    { hom := a
      inv := b
      hom_inv_id := by
        apply (cancel_mono a).mp
        simp only [Category.assoc, hba, Category.comp_id, Category.id_comp]
      inv_hom_id := hba }
  exact e.isIso_hom

end Construction.RationalPointResidue

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalPoint
