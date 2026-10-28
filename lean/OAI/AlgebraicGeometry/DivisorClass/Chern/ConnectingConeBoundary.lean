import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-! # Connecting Cone Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingConeBoundary

noncomputable section

/-! An explicit mapping-cone boundary for computing an actual connecting class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ)) {K : CochainComplex C ℤ}
  (a : S.X₁ ⟶ K) (b : Cochain S.X₂ K 0) (z : Cocycle S.X₃ K 1)
  (hb : (Cochain.ofHom S.f).comp b (zero_add 0) = Cochain.ofHom a)
  (hd : δ 0 1 b = (Cochain.ofHom S.g).comp z.val (zero_add 1))

include hb hd in
theorem connectingCone_boundary :
    δ 0 1 (mappingCone.descCochain S.f (0 : Cochain S.X₁ K (-1)) b (by decide)) =
      (z.precomp (mappingCone.descShortComplex S)).val -
        ((mappingCone.fst S.f).postcomp a).val := by
  rw [mappingCone.δ_descCochain _ _ _ _ 1 rfl, δ_zero, zero_add, hb, hd]
  simp only [Int.negOnePow_one, Units.smul_def, Units.val_neg, Units.val_one,
    neg_one_zsmul, Cochain.comp_neg, Cocycle.precomp_coe, Cocycle.postcomp_coe]
  have he : (Cochain.ofHom (mappingCone.descShortComplex S)).comp z.val (zero_add 1) =
      (mappingCone.snd S.f).comp ((Cochain.ofHom S.g).comp z.val (zero_add 1)) (zero_add 1) := by
    rw [mappingCone.descShortComplex, mappingCone.ofHom_desc]
    simp only [mappingCone.descCochain, Cochain.comp_zero, zero_add]
    exact Cochain.comp_assoc_of_second_is_zero_cochain (mappingCone.snd S.f)
      (Cochain.ofHom S.g) z.val (zero_add 1)
  rw [he]
  abel

include hb hd in
theorem connectingCone_cohomologyClass :
    CohomologyClass.mk (z.precomp (mappingCone.descShortComplex S)) =
      CohomologyClass.mk ((mappingCone.fst S.f).postcomp a) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨0, rfl, mappingCone.descCochain S.f (0 : Cochain S.X₁ K (-1)) b (by decide),
    connectingCone_boundary S a b z hb hd⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingConeBoundary
