import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeBaseChange
import Mathlib.Algebra.CharP.Algebra

/-! # Char Zero Field Parameters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharZeroFieldParameters.Construction

noncomputable section

/-! Every field-valued parameter of a scheme over a characteristic-zero
field has characteristic zero, including its canonical residue fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem field_charZero_of_map_to_charZero_field
    {k K : Type u} [Field k] [CharZero k] [Field K]
    (s : Spec (.of K) ⟶ Spec (.of k)) : CharZero K := by
  let c : CommRingCat.of k ⟶ CommRingCat.of K :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom
  exact charZero_of_injective_ringHom c.hom.injective

theorem residueField_charZero_of_map_to_field
    {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}}
    (p : S ⟶ Spec (.of k)) (s : S) : CharZero (S.residueField s) :=
  field_charZero_of_map_to_charZero_field (S.fromSpecResidueField s ≫ p)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharZeroFieldParameters.Construction
