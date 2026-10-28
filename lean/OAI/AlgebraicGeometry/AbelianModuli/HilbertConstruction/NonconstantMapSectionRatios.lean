import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingRatios
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.AffineCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineRangeConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackSectionBound

/-! # Nonconstant Map Section Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonconstantMapSectionRatios

noncomputable section

/-! Every nonconstant map from a proper integral scheme into a power-projectively embedded scheme has a transcendental ratio among the pulled-back embedding sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of K)) [UniversallyClosed p] (q : Y ⟶ Spec (.of K))
variable {L : Line.Bundles.LineBundle Y} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L q)

theorem nonconstantMap_exists_transcendentalSectionRatio (f : X ⟶ Y)
    (hf : ¬ ∃ a : Spec (.of K) ⟶ Y, p ≫ a = f) :
    ∃ k j : Fin (E.dimension + 1),
      Nonempty (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f (E.sections k))) ∧
      Transcendental K (show Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p)
        (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f (E.sections k))) from
        Section.ComponentRatios.sectionComponentRatio (Ample.LineBundles.pullbackSection f (E.sections k)) (Ample.LineBundles.pullbackSection f (E.sections j))
          (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f (E.sections k))) le_rfl) := by
  let s := fun j => Ample.LineBundles.pullbackSection f (E.sections j)
  have hs : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (s j) := by
    intro x
    obtain ⟨j, hj⟩ := E.covers (f x)
    refine ⟨j, ?_⟩
    change x ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f (E.sections j))
    rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange f E.power]
    exact hj
  obtain ⟨k, hk⟩ := Generated.PullbackSectionBound.generatingSections_pullback_nonempty f E.power E.sections E.covers
  have : Nonempty (Ample.LineBundles.sectionNonvanishing (s k)) := hk
  have hnot : ¬ IsIso (s k) := by
    intro h
    have ht : f ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing (E.sections k) = ⊤ :=
      (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange f E.power (E.sections k)).symm.trans
        ((Section.Frames.isIso_iff_sectionNonvanishing_eq_top (s k)).mp h)
    exact hf (Proper.AffineRangeConstants.properIntegral_map_constant_of_affine_range p f (Ample.LineBundles.sectionNonvanishing (E.sections k))
      (E.sectionChart_isAffine q k) ht)
  obtain ⟨j, hj⟩ := @GeneratingRatios.generatingSections_exists_transcendentalRatio K _ _ X _ p
    (E.power.pullback f) _ s hs k hk hnot
  exact ⟨k, j, hk, hj⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonconstantMapSectionRatios
