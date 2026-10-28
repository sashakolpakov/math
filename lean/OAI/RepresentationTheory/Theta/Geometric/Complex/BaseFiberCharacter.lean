import OAI.RepresentationTheory.Theta.Geometric.Reference.LieSignature
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingLieIndices

/-! # Base Fiber Character -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.BaseFiberCharacter

noncomputable section

/-! Evaluation of the literal reference action on a complex test point
recovers the original distinguished embedding and its rank two. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingLieIndices

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

omit [NumberField.IsCMField E] in
theorem referenceComplexBaseAction_fiber (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp
      (x.left.appTop.hom.comp (S.hom.appTop.hom.comp (Reference.LieSignature.referenceComplexBaseAction P))) =
      P.μ.comp (algebraMap (NumberField.RingOfIntegers E) E) := by
  have he : x.left.appTop.hom.comp S.hom.appTop.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, x.w]
    rfl
  apply RingHom.ext
  intro a
  have ha := RingHom.congr_fun he (Reference.LieSignature.referenceComplexBaseAction P a)
  exact (congrArg (Scheme.ΓSpecIso (.of ℂ)).hom ha).trans
    ((Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.apply_symm_apply _)

theorem reference_lieRank_identity (hP : P.IsAdmissible) : P.lieRank (AlgEquiv.refl : E ≃ₐ[ℚ] E) = 2 :=
  (P.lieRank_of_embedding hP (AlgEquiv.refl : E ≃ₐ[ℚ] E) P.distinguished (RingHom.comp_id _)).trans (ite_eq_left rfl)

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.BaseFiberCharacter
