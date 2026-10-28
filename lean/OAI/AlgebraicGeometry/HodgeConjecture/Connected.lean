import OAI.AlgebraicGeometry.HodgeConjecture.Surface
import OAI.AlgebraicGeometry.HodgeConjecture.FourProduct
import OAI.AlgebraicGeometry.AbelianVariety.PowerImage
import Mathlib.Analysis.Convex.PathConnected

/-! # Connected -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Connected.CM.SurfaceConstruction

noncomputable section

/-! Connectedness needed by the top-degree trace argument, derived from
the actual ball cover and the categorical abelian product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

theorem ballDomain_pathConnected (E : IntermediateField ℚ ℂ)
    [NumberField E] [NumberField.IsCMField E] (B : HeckeCycles.GeometricSource.CM.BallDatum E) :
    PathConnectedSpace B.Domain := by
  have hzero : (0 : HeckeCycles.GeometricSource.CM.BallChart) ∈ B.domain := by
    change Complex.normSq 0 + Complex.normSq 0 < -(B.b : ℂ).re
    simpa using neg_pos.mpr B.negative
  have hstar : StarConvex ℝ (0 : HeckeCycles.GeometricSource.CM.BallChart) B.domain := by
    intro z hz a b ha hb hab
    change Complex.normSq ((a • (0 : HeckeCycles.GeometricSource.CM.BallChart) + b • z) 0) +
      Complex.normSq ((a • (0 : HeckeCycles.GeometricSource.CM.BallChart) + b • z) 1) < -(B.b : ℂ).re
    simp only [smul_zero, zero_add, Pi.smul_apply]
    change Complex.normSq ((b : ℂ) * z 0) + Complex.normSq ((b : ℂ) * z 1) < _
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
    have hz' : Complex.normSq (z 0) + Complex.normSq (z 1) < -(B.b : ℂ).re := hz
    have hb1 : b ≤ 1 := by linarith
    have hb2 : b * b ≤ 1 := by nlinarith
    have hz0 := Complex.normSq_nonneg (z 0)
    have hz1 := Complex.normSq_nonneg (z 1)
    nlinarith [mul_le_mul_of_nonneg_right hb2 (add_nonneg hz0 hz1)]
  exact (isPathConnected_iff_pathConnectedSpace).mp (hstar.isPathConnected hzero)

theorem ballSurface_pathConnected (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    {B : HeckeCycles.GeometricSource.CM.BallDatum E} {N : ℕ}
    (S : ThetaCycle.Cm.PrincipalBallSurface E B N) : PathConnectedSpace S.surface.variety.analyticSpace := by
  let : PathConnectedSpace B.Domain := ballDomain_pathConnected E B
  exact S.isBallCover.2.1.pathConnectedSpace S.isBallCover.2.2.1.continuous

theorem abelian_pathConnected (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : PathConnectedSpace A.variety.analyticSpace := by
  let : ConnectedSpace A.variety.analyticSpace := AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  let : LocallyPathConnectedSpace A.variety.analyticSpace :=
    AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  exact PathConnectedSpace.of_locallyPathConnectedSpace

theorem projectiveProduct_pathConnected (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace] :
    PathConnectedSpace (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).analyticSpace := by
  let e := AlgebraicTopology.Kunneth.Add.Construction.productPointHomeomorph
    (Z := (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X).presentation)
    (fst S.toOver X.toOver) (snd S.toOver X.toOver) (tensorProductIsBinaryProduct _ _)
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

theorem fourAbelianProduct_pathConnected (A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : ∀ i, X.toOver ⟶ (A i).toOver)
    (hprod : IsLimit (Fan.mk X.toOver π)) : PathConnectedSpace X.analyticSpace := by
  let : ∀ i, PathConnectedSpace (A i).variety.analyticSpace := fun i => abelian_pathConnected (A i)
  let B01 := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety (A 0).variety (A 1).variety
  let B23 := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety (A 2).variety (A 3).variety
  let : PathConnectedSpace B01.analyticSpace := projectiveProduct_pathConnected _ _
  let : PathConnectedSpace B23.analyticSpace := projectiveProduct_pathConnected _ _
  let e := AlgebraicTopology.Kunneth.Add.Construction.productPointHomeomorph
    (X := B01.presentation) (Y := B23.presentation) (Z := X.presentation)
    (FourProduct.CM.SurfaceConstruction.firstPairMap π) (FourProduct.CM.SurfaceConstruction.lastPairMap π) (FourProduct.CM.SurfaceConstruction.fourProduct_isBinaryProduct π hprod)
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

end

end OAI.AlgebraicGeometry.HodgeConjecture.Connected.CM.SurfaceConstruction
