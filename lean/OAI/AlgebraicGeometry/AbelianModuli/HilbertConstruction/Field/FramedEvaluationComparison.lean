import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionValueChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.LineBundleEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FrameOpenCover

/-! # Framed Evaluation Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FramedEvaluationComparison

noncomputable section

/-! Any actual frame of a rational line-bundle fiber gives the canonical
rational evaluation functional up to one nonzero scalar, uniformly for
all global sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]

theorem rationalPointGlobalEvaluation_identity :
    Rational.PointGlobalEvaluation.rationalPointGlobalEvaluation (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) (Category.id_comp _) =
      (Scheme.ΓSpecIso (.of K)).hom.hom := by
  let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  ext a
  obtain ⟨r, rfl⟩ := e.symm.surjective a
  have h := Rational.PointGlobalEvaluation.rationalPointGlobalEvaluation_coefficient
    (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) (Category.id_comp _) r
  have hc : Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))) r = e.symm r := by
    change (Scheme.Hom.appTop (𝟙 (Spec (.of K)))) ((Scheme.ΓSpecIso (.of K)).inv r) = _
    simp only [Scheme.Hom.id_appTop]
    rfl
  rw [hc] at h
  exact h.trans (e.apply_symm_apply r).symm

theorem fieldFramedSectionValue_eq_unit_mul
    {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) (x : Spec (.of K) ⟶ X)
    (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule (Spec (.of K))) :
    ∃ u : Kˣ, ∀ a : Line.Bundles.structureModule X ⟶ L.sheaf,
      Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K))) (Family.FramedSectionEvaluation.familyFramedSectionValue L x e a) =
        (u : K) * Rational.LineBundleEvaluation.rationalLineBundleSectionValue L x a := by
  let c := Local.SpectrumLineBundleFrames.localSpectrumLineBundleIso (L.pullback x)
  obtain ⟨v, hv⟩ := Framed.SectionValueChange.familyFramedSectionValue_change L x c e
  let φ := Geometric.FrameOpenCover.fieldPointGlobalScalarMap (𝟙 (Spec (.of K)))
  refine ⟨Units.map φ.toMonoidHom v, fun a => ?_⟩
  rw [hv a, map_mul]
  change φ (v : Γ(Spec (.of K), ⊤)) * φ (Family.FramedSectionEvaluation.familyFramedSectionValue L x c a) =
    φ (v : Γ(Spec (.of K), ⊤)) * Rational.LineBundleEvaluation.rationalLineBundleSectionValue L x a
  congr 1
  unfold Rational.LineBundleEvaluation.rationalLineBundleSectionValue
  rw [rationalPointGlobalEvaluation_identity]
  change (Scheme.ΓSpecIso (.of K)).hom ((Scheme.Hom.appTop (𝟙 (Spec (.of K))))
    (Family.FramedSectionEvaluation.familyFramedSectionValue L x c a)) = _
  rw [Scheme.Hom.id_appTop]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FramedEvaluationComparison
