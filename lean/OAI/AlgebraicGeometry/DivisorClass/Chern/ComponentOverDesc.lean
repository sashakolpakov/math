import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology

/-! # Component Over Desc -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentOverDesc

noncomputable section

/-! Morphisms on the original integral components glue through the original scheme coproduct isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def componentOverDesc (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {T : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : ∀ C : irreducibleComponents P.carrier, (P.componentVariety C).toOver ⟶ T) : P.toOver ⟶ T :=
  P.componentCoproductOverIso.inv ≫ Over.homMk (Sigma.desc (fun C => (f C).left)) (by
    change Sigma.desc (fun C => (f C).left) ≫ T.hom =
      Sigma.desc (fun C => (P.componentVariety C).structureMap)
    apply Sigma.hom_ext
    intro C
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact (f C).w)

theorem componentOverDesc_restrict (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {T : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : ∀ C : irreducibleComponents P.carrier, (P.componentVariety C).toOver ⟶ T)
    (C : irreducibleComponents P.carrier) :
    P.componentInclusionOver C ≫ componentOverDesc P f = f C := by
  apply Over.OverMorphism.ext
  change P.componentInclusion C ≫
    (P.componentCoproductIso.inv ≫ Sigma.desc (fun C => (f C).left)) = (f C).left
  rw [← P.componentCoproductIso_ι_hom, Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_comp_desc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentOverDesc
