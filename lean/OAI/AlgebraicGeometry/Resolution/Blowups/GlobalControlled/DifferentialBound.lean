import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Chart
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialUnitGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Differential Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.DifferentialBound.Construction

noncomputable section

/-! Differential-order bounds for the actual globally transformed ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The complex structure on the explicit Rees ring is the structure
induced by its actual map to the original complex ambient scheme. -/
theorem globalBlowupReesChart_complex_structure (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) (a : I.ideal U) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    Chart.Construction.globalBlowupReesChart I hI U a ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) =
      ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (Blowup.Charts.Construction.blowupChart (I.ideal U) a) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  rw [← Category.assoc, Chart.Construction.globalBlowupReesChart_over, Category.assoc,
    ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp]
  rfl

/-- A differential unit bound on every actual Rees chart gives the same
bound for the native global controlled ideal sheaf. -/
theorem globalBlowupControlledIdeal_differential_top (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (b n : ℕ) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hlocal : ∀ U : X.affineOpens, letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
      ∀ a : I.ideal U, Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ
        (ControlledTransform.Construction.blowupControlledTransform (I.ideal U) (J.ideal U) b a) n = ⊤) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (Ideal.Construction.globalBlowupControlledIdeal I J hI b) n = ⊤ := by
  apply DifferentialUnitGluing.Construction.idealSheaf_eq_top_of_openCover _ (Chart.Construction.globalBlowupReesAffineCover I hI).openCover
  intro p
  change (Σ U : X.affineOpens, I.ideal U) at p
  let : Algebra ℂ Γ(X, p.1) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f p.1
  exact DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_unit_on_affine (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
    (Ideal.Construction.globalBlowupControlledIdeal I J hI b) n (Chart.Construction.globalBlowupReesChart I hI p.1 p.2)
    (globalBlowupReesChart_complex_structure f I hI p.1 p.2)
    (ControlledTransform.Construction.blowupControlledTransform (I.ideal p.1) (J.ideal p.1) b p.2)
    (Chart.Construction.globalBlowupControlledIdeal_comap_reesChart I J hI b p.1 p.2) (hlocal p.1 p.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.DifferentialBound.Construction
