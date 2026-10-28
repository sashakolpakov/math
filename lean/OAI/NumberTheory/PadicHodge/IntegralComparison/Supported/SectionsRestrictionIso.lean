import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsRestriction

/-! # Sections Restriction Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsRestrictionIso

noncomputable section

/-! Restriction between two neighborhoods of the same support is an
isomorphism, on the actual section kernels and their cochain complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {D : Type u} [Category.{v} D] [Abelian D] {X : TopCat.{w}}
  (O U V : Opens X) (h : V ≤ U) (hU : U ⊔ O = ⊤) (hV : V ⊔ O = ⊤)
open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision

include hU hV in
theorem map_isIso : IsIso (SectionsRestriction.map (D := D) O U V h) := by
  have hm : SectionsRestriction.map (D := D) O U V h =
      (SectionsExcision.excisionIso O U hU).inv ≫ (SectionsExcision.excisionIso O V hV).hom := by
    apply (cancel_epi (SectionsExcision.excisionIso (D := D) O U hU).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact SectionsRestriction.excision_square O U V h
  rw [hm]
  infer_instance

include hU hV in
theorem complex_isIso (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ) :
    IsIso (SectionsRestriction.complex O U V h K) := by
  let := map_isIso (D := D) O U V h hU hV
  let (q : ℕ) : IsIso ((SectionsRestriction.complex O U V h K).f q) := by
    change IsIso ((SectionsRestriction.map O U V h).app (K.X q))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsRestrictionIso
