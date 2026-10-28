import OAI.AlgebraicGeometry.Resolution.Blowups.Open.CoverDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.DifferentialBound

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Dimension.Construction

noncomputable section

/-! Actual smooth global blowups retain the ambient dimension bound on every affine atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

theorem globalBlowup_dimension_le (I : X.IdealSheafData) (hI : I ≠ ⊥)
    [Smooth (Data.Construction.globalBlowupToBase I hI ≫ f)] (d : WithBot ℕ∞) (hd : topologicalKrullDim X ≤ d) :
    topologicalKrullDim (Data.Construction.globalBlowup I hI) ≤ d := by
  let C := GlobalControlled.Chart.Construction.globalBlowupReesAffineCover I hI
  refine Open.CoverDimension.Construction.scheme_dimension_le_of_open_affine_cover C.X C.f ?_ d ?_
  · intro x
    exact ⟨C.idx x, C.covers x⟩
  · intro p
    change (Σ U : X.affineOpens, I.ideal U) at p
    let : Algebra ℂ Γ(X, p.1) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f p.1
    let : Algebra.Smooth ℂ Γ(X, p.1) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f p.1
    let R := Blowup.Charts.Construction.blowupChart (I.ideal p.1) p.2
    let j := GlobalControlled.Chart.Construction.globalBlowupReesChart I hI p.1 p.2
    have hj : j ≫ (Data.Construction.globalBlowupToBase I hI ≫ f) = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R :=
      GlobalControlled.DifferentialBound.Construction.globalBlowupReesChart_complex_structure f I hI p.1 p.2
    let : Algebra.Smooth ℂ R := by
      have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := hj ▸ inferInstanceAs (Smooth (j ≫ (Data.Construction.globalBlowupToBase I hI ≫ f)))
      exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
        (φ := CommRingCat.ofHom (algebraMap ℂ R))).mp hs)
    have hR : ringKrullDim R ≤ ringKrullDim Γ(X, p.1) :=
      Blowups.Smooth.BlowupDimension.Construction.blowupChart_ringKrullDim_le_of_finiteType ℂ (I.ideal p.1) p.2
    let : IsOpenImmersion p.1.2.fromSpec := p.1.2.isOpenImmersion_fromSpec
    exact hR.trans ((Open.CoverDimension.Construction.ringKrullDim_le_of_affine_open_map Γ(X, p.1) p.1.2.fromSpec).trans hd)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Dimension.Construction
