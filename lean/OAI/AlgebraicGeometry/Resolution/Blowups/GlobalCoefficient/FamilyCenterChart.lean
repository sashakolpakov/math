import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientFamilyCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.AffineCharts
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Family Center Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCenterChart.Construction

noncomputable section

/-! Native smooth centers lift permissibly from retained coefficient lower bounds on actual hypersurface charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem global_coefficient_family_center_permissible_on_chart
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J H : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (hHI : H ≤ I)
    (C : H.subscheme.IdealSheafData) (b : ℕ) (hC : C ≤ (I.comap H.subschemeι) ^ b.factorial)
    (U : X.affineOpens) (z : Γ(X, U)) (hHz : H.ideal U = Ideal.span {z}) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    ∀ (D : Derivation ℂ Γ(X, U) Γ(X, U)), D z = 1 →
      ∀ {τ : Type} (p : τ → Γ(X, U)), Ideal.span (Set.range p) = J.ideal U →
      ∀ (l : Spec (.of (Γ(X, U) ⧸ Ideal.span {z})) ⟶ H.subscheme),
        l ≫ H.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {z}))) ≫ U.2.fromSpec →
      ∀ (C₀ : Ideal (Γ(X, U) ⧸ Ideal.span {z})), C.comap l = Affine.QuotientKernel.Construction.affineQuotientKernel C₀ →
        WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C₀ → J.ideal U ≤ I.ideal U ^ b := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℚ Γ(X, U) := ((algebraMap ℂ Γ(X, U)).comp (algebraMap ℚ ℂ)).toAlgebra
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let : Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U) := Global.SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f I U
  intro D hD τ p hp l hl C₀ hC₀ hlow
  have hzI : z ∈ I.ideal U := (hHI U) (by rw [hHz]; exact Ideal.mem_span_singleton_self z)
  have hbound : C₀ ≤ ((I.ideal U).map (Ideal.Quotient.mk (Ideal.span {z}))) ^ b.factorial := by
    apply (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp
    rw [Affine.QuotientKernel.Construction.affineQuotientKernel_pow, ← hC₀]
    have he : (I.comap H.subschemeι).comap l =
        Affine.QuotientKernel.Construction.affineQuotientKernel ((I.ideal U).map (Ideal.Quotient.mk (Ideal.span {z}))) := by
      rw [← Scheme.IdealSheafData.comap_comp, hl]
      exact Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel I U (Ideal.Quotient.mk (Ideal.span {z}))
    rw [← he, ← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow]
    exact Scheme.IdealSheafData.comap_mono l hC
  rw [← hp]
  exact (Blowups.Smooth.CoefficientFamilyCenter.Construction.smooth_center_iff_weighted_normal_family ℂ (I.ideal U) z hzI D hD p b).mpr
    (hlow.trans hbound)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCenterChart.Construction
