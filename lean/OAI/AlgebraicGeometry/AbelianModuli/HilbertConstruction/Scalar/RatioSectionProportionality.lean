import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ScalarSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralLineBundleRestrictions

/-! # Ratio Section Proportionality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.RatioSectionProportionality

noncomputable section

/-! A scalar ratio on a nonempty frame open of an integral scheme forces the two global sections to be proportional over the coefficient field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]

theorem sectionCoordinateLinear_injective (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (U : X.Opens) (hU : U ≤ Ample.LineBundles.sectionNonvanishing s)
    [Nonempty U] : Function.Injective (Coefficient.SectionCoordinates.sectionCoordinateLinear p s U hU) :=
  (Coefficient.SectionCoordinates.coefficientFrameCoordinateEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) U
    (Section.LocalLinearFrames.sectionLocalFrameEquiv s U hU).symm).injective.comp (L.restriction_injective U.leTop.le)

omit [IsIntegral X] in
theorem sectionComponentRatio_self {M : X.Modules} (s : Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ Ample.LineBundles.sectionNonvanishing s) : Section.ComponentRatios.sectionComponentRatio s s U hU = 1 := by
  apply (Section.LocalLinearFrames.sectionLocalFrameEquiv s U hU).injective
  exact ((Section.LocalLinearFrames.sectionLocalFrameEquiv s U hU).apply_symm_apply _).trans
    (Section.LocalLinearFrames.sectionLocalFrameEquiv_apply s U hU 1).symm

theorem section_eq_scalar_of_ratio (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)
    (s t : Line.Bundles.structureModule X ⟶ L.sheaf) (U : X.Opens) (hU : U ≤ Ample.LineBundles.sectionNonvanishing s)
    [Nonempty U] (c : K)
    (hc : algebraMap K (Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p) U) c =
      Section.ComponentRatios.sectionComponentRatio s t U hU) : t = Coefficient.ScalarSections.coefficientScalarSection p c s := by
  apply (Global.Sections.moduleSectionHomEquiv L.sheaf).injective
  apply sectionCoordinateLinear_injective p L s U hU
  let φ := Coefficient.SectionCoordinates.sectionCoordinateLinear p s U hU
  have hself : φ (Global.Sections.moduleSectionHomEquiv L.sheaf s) = 1 :=
    (Coefficient.SectionCoordinates.sectionCoordinateLinear_value p s s U hU).trans (sectionComponentRatio_self s U hU)
  have hscalar : φ (Global.Sections.moduleSectionHomEquiv L.sheaf (Coefficient.ScalarSections.coefficientScalarSection p c s)) =
      c • (1 : Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p) U) :=
    (congrArg φ (Coefficient.ScalarSections.coefficientScalarSection_value p c s)).trans
      ((φ.map_smul c _).trans (congrArg (fun z : Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Coefficient.ModulePresheaf.schemeCoefficientMap p) U => c • z) hself))
  apply (Coefficient.SectionCoordinates.sectionCoordinateLinear_value p s t U hU).trans
  apply Eq.trans _ hscalar.symm
  simpa only [Algebra.smul_def, mul_one] using hc.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.RatioSectionProportionality
