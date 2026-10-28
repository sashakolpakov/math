import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ChartDerivations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineChartDimension
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Affine Derivation Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDerivationChart

noncomputable section

/-! The actual native affine regular atlas contains charts whose
derivatives give the canonical complex derivation space at every point. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
open scoped ContDiff

theorem exists_smoothDomain_derivation_chart {S : Type*} [CommRing S] [Algebra ℂ S]
    [IsDomain S] [Algebra.Smooth ℂ S] (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S) → ℂ),
      e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S) ∧ x ∈ e.source ∧
      ∀ u ∈ e.target,
        ∃ d : (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S) → ℂ) ≃ₗ[ℂ] PointDerivations.pointDerivations (e.symm u),
          ∀ v a, (d v).val a = fderiv ℂ (fun w => e.symm w a) u v := by
  classical
  obtain ⟨g, hg, n, m, P, e0, hx, hs, hcoords, hreg, hdual⟩ := ReferenceFamily.Smooth.AffineDualChart.exists_smoothAffine_dual_chart x
  have hgne : g ≠ 0 := by
    intro hz
    exact hg (hz ▸ x.map_zero)
  have hdim : Fintype.card (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) = Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ S :=
    AffineChartDimension.principalSmooth_free_dimension g hgne P
  have hex := Finite.ChartDerivations.finiteChart_derivations x g e0 hx (fun y hy => hs hy) hcoords hreg hdual
  exact hdim ▸ hex

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDerivationChart
