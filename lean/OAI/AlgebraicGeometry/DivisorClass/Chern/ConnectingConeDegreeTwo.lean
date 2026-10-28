import OAI.AlgebraicGeometry.DivisorClass.Chern.CocycleComposition

/-! # Connecting Cone Degree Two -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingConeDegreeTwo

noncomputable section

/-! The degree-one cone primitive for composing an extension with a degree-one cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ)) {K : CochainComplex C ℤ}
  (a : Cocycle S.X₁ K 1) (b : Cochain S.X₂ K 1) (z : Cocycle S.X₃ K 2)
  (hb : (Cochain.ofHom S.f).comp b (zero_add 1) = a.val)
  (hd : δ 1 2 b = (Cochain.ofHom S.g).comp z.val (zero_add 2))

include hb hd in
theorem connectingCone_degreeTwo_boundary :
    δ 1 2 (mappingCone.descCochain S.f (0 : Cochain S.X₁ K 0) b (by decide)) =
      (z.precomp (mappingCone.descShortComplex S)).val +
        (CocycleComposition.cocycleOneComp (mappingCone.fst S.f) a).val := by
  rw [mappingCone.δ_descCochain _ _ _ _ 2 rfl, δ_zero, zero_add, hb, hd]
  simp only [show (2 : ℤ).negOnePow = 1 from rfl, one_smul, Cocycle.precomp_coe]
  have he : (Cochain.ofHom (mappingCone.descShortComplex S)).comp z.val (zero_add 2) =
      (mappingCone.snd S.f).comp ((Cochain.ofHom S.g).comp z.val (zero_add 2)) (zero_add 2) := by
    rw [mappingCone.descShortComplex, mappingCone.ofHom_desc]
    simp only [mappingCone.descCochain, Cochain.comp_zero, zero_add]
    exact Cochain.comp_assoc_of_second_is_zero_cochain (mappingCone.snd S.f)
      (Cochain.ofHom S.g) z.val (zero_add 2)
  rw [he]
  exact add_comm _ _

include hb hd in
theorem connectingCone_degreeTwo_cohomologyClass :
    CohomologyClass.mk (z.precomp (mappingCone.descShortComplex S)) =
      CohomologyClass.mk (-CocycleComposition.cocycleOneComp (mappingCone.fst S.f) a) := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨1, rfl, mappingCone.descCochain S.f (0 : Cochain S.X₁ K 0) b (by decide), ?_⟩
  rw [Cocycle.coe_sub, Cocycle.coe_neg, sub_neg_eq_add]
  exact connectingCone_degreeTwo_boundary S a b z hb hd

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingConeDegreeTwo
