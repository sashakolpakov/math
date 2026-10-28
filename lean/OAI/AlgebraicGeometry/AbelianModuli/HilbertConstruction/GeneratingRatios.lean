import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.RatioSectionProportionality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraicallyClosedConstants

/-! # Generating Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingRatios

noncomputable section

/-! If all ratios in a generating family are algebraic over an algebraically closed ground field, any nonzero denominator section is a global frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {ι : Type v}
variable (s : ι → (Line.Bundles.structureModule X ⟶ L.sheaf)) (hs : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (s j))

include hs

theorem generatingSections_frame_of_algebraicRatios (k : ι) [Nonempty (Ample.LineBundles.sectionNonvanishing (s k))]
    (h : ∀ j, IsAlgebraic K (show Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p) (Ample.LineBundles.sectionNonvanishing (s k)) from
      Section.ComponentRatios.sectionComponentRatio (s k) (s j) (Ample.LineBundles.sectionNonvanishing (s k)) le_rfl)) : IsIso (s k) := by
  let U := Ample.LineBundles.sectionNonvanishing (s k)
  have : IsDomain (Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p) U) := inferInstanceAs (IsDomain Γ(X, U))
  have ht (j : ι) : ∃ c : K, s j = Coefficient.ScalarSections.coefficientScalarSection p c (s k) := by
    obtain ⟨c, hc⟩ := AlgebraicallyClosedConstants.algebraic_is_scalar
      (show Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p) U from Section.ComponentRatios.sectionComponentRatio (s k) (s j) U le_rfl) (h j)
    exact ⟨c, Scalar.RatioSectionProportionality.section_eq_scalar_of_ratio p L (s k) (s j) U le_rfl c hc⟩
  apply (Section.Frames.isIso_iff_sectionNonvanishing_eq_top (s k)).mpr
  apply le_antisymm le_top
  intro x _
  obtain ⟨j, hj⟩ := hs x
  obtain ⟨c, hc⟩ := ht j
  exact Coefficient.ScalarSections.coefficientScalarSection_nonvanishing_le p L c (s k) ((congrArg (fun t => x ∈ Ample.LineBundles.sectionNonvanishing t) hc).mp hj)

theorem generatingSections_exists_transcendentalRatio (k : ι) [Nonempty (Ample.LineBundles.sectionNonvanishing (s k))]
    (hk : ¬ IsIso (s k)) :
    ∃ j, Transcendental K (show Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p) (Ample.LineBundles.sectionNonvanishing (s k)) from
      Section.ComponentRatios.sectionComponentRatio (s k) (s j) (Ample.LineBundles.sectionNonvanishing (s k)) le_rfl) := by
  by_contra h
  apply hk
  apply generatingSections_frame_of_algebraicRatios p L s hs k
  intro j
  exact Classical.byContradiction (fun hj => h ⟨j, hj⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingRatios
