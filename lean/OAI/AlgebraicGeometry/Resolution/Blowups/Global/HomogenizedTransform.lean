import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialTransform

/-! # Homogenized Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizedTransform.Construction

noncomputable section

/-! Homogenized comparison intervals survive each actual global permissible blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem globalBlowupControlledIdeal_mono (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (b : ℕ) {J L : X.IdealSheafData} (h : J ≤ L) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b ≤ GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI b := by
  intro U
  exact Submodule.colon_mono ((Scheme.IdealSheafData.comap_mono (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) h) U) le_rfl

variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

omit [Smooth f] in
theorem globalBlowupControlledIdeal_homogenized_comap_reesChart
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b n : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (U : X.affineOpens) (a : I.ideal U) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    (Homogenization.Construction.smoothHomogenizedIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) n).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) =
        Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ
          (ControlledTransform.Construction.blowupControlledTransform (I.ideal U) (J.ideal U) b a) n) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  exact HomogenizationRestriction.Construction.smoothHomogenizedIdealSheaf_comap_affine (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) n (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a)
    (GlobalControlled.DifferentialBound.Construction.globalBlowupReesChart_complex_structure f I hI U a) _
    (GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart I J hI b U a)

theorem globalBlowup_homogenized_controlled_le_on_chart (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (n : ℕ) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (hperm : J ≤ I ^ (n + 1)) :
    ∀ (U : X.affineOpens) (a : I.ideal U),
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) hI (n + 1)).comap
      (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) ≤
      (Homogenization.Construction.smoothHomogenizedIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) := by
  intro U a
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart I (Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) hI (n + 1) U a,
    globalBlowupControlledIdeal_homogenized_comap_reesChart f I J hI (n + 1) n U a,
    Homogenization.Construction.smoothHomogenizedIdealSheaf_ideal f J n U]
  exact DifferentialTransform.Construction.affineQuotientKernel_mono
    (Relative.HomogenizationTransform.Construction.relativeHomogenizedIdeal_controlledTransform_le ℂ (I.ideal U) (J.ideal U) a n (hperm U))

theorem globalBlowup_homogenized_controlled_le (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (n : ℕ) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (hperm : J ≤ I ^ (n + 1)) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) hI (n + 1) ≤
      Homogenization.Construction.smoothHomogenizedIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n := by
  exact IdealSheaf.EqualityGluing.Construction.idealSheaf_le_of_openCover _ _ (GlobalControlled.Chart.Construction.globalBlowupReesAffineCover I hI).openCover
    (fun p => globalBlowup_homogenized_controlled_le_on_chart f I J hI n hperm p.1 p.2)

theorem global_homogenized_interval_preserved (I J L : X.IdealSheafData)
    (hI : I ≠ ⊥) (n : ℕ) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hJL : J ≤ L) (hLH : L ≤ Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) (hL : L ≤ I ^ (n + 1)) :
    J ≤ I ^ (n + 1) ∧
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1) ≤ GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI (n + 1) ∧
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI (n + 1) ≤
        Homogenization.Construction.smoothHomogenizedIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n := by
  have hJ := hJL.trans hL
  exact ⟨hJ, globalBlowupControlledIdeal_mono I hI (n + 1) hJL,
    (globalBlowupControlledIdeal_mono I hI (n + 1) hLH).trans
      (globalBlowup_homogenized_controlled_le f I J hI n hJ)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizedTransform.Construction
