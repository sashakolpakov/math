import OAI.ArithmeticGeometry.Descent.CMVariety.FiberEndomorphismCoordinates
import OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative
import OAI.ArithmeticGeometry.Descent.CMVariety.MultiplicationDerivative
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

/-! # Intrinsic Family Endomorphism Derivative -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyEndomorphismDerivative.Abelian.RelativeCharts

noncomputable section

/-!
Construct continuous derivative matrices of the actual family
endomorphism in the relative tangent coordinates. Analytic coordinate
dependence and its equality with the genuine native fiber derivative
are proved from the given algebraic morphism and fiber-inclusion square.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps Set
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj _root_.Topology

variable {R A E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
  {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A} {σ : A →ₐ[ℂ] R}

theorem exists_continuous_native_familyEndomorphism_derivative
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (k : G.scheme ⟶ G.scheme) [IsMonHom k]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ AbelianFamilyPoints.FamilyPoints.total S G) [IsOpenImmersion i.left]
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ)
    (hx : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x ≫
        AbelianFamilyPoints.FamilyPoints.projection S G) ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G)
    (s : F → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    [∀ q, IsIntegral (G.pullback (s q).left).scheme.left]
    (c : ∀ q, OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) E)
    (hc : ∀ q ∈ N.neighborhood,
      (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) ∈ (c q).source ∧ c q 1 = 0 ∧
      (c q).MDifferentiable
        (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ))
        (𝓘(ℝ, E)) ∧
      (c q).source = (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q))) ⁻¹'
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).source ∧
      (c q).target = {v | (q, v) ∈ N.charts.total.target} ∧
      (∀ z ∈ (c q).source, c q z =
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)).2) ∧
      ∀ v ∈ (c q).target,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) ((c q).symm v) =
          (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i N.charts.total).symm (q, v)) :
    ∃ (U : Set F) (derivative : F → E →L[ℝ] E),
      IsOpen U ∧ N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A)) ∈ U ∧
      U ⊆ N.neighborhood ∧ ContinuousOn derivative U ∧
      ∀ q ∈ U, ∀ v : E,
        ChartEndomorphismDerivative.Abelian.chartTangentMap
            (E := Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ)
            (c q) (derivative q v) =
          mfderiv
            (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ))
            (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ))
            (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (s q))) 1
            (ChartEndomorphismDerivative.Abelian.chartTangentMap
              (E := Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ)
              (c q) v) := by
  obtain ⟨D, hD, hD₀, htarget, hmap, himage⟩ :=
    FamilyEndomorphismCharts.Abelian.RelativeCharts.exists_analytic_familyEndomorphism_coordinates G k i N hx
  let f := fun z : F × E => (FamilyEndomorphismCharts.Abelian.RelativeCharts.familyEndomorphismCoordinates G k i N z).2
  have hf : ContDiffOn ℝ 2 f D := (hmap.snd.restrict_scalars ℝ).of_le (by simp)
  let derivative := fun q : F => fderiv ℝ (fun v => f (q, v)) 0
  let U := N.neighborhood ∩ {q : F | (q, (0 : E)) ∈ D}
  have hU : IsOpen U := N.isOpen.inter (hD.preimage (continuous_id.prodMk continuous_const))
  refine ⟨U, derivative, hU, ⟨N.center, hD₀⟩, inter_subset_left,
    (MultiplicationDerivative.Abelian.continuousOn_parameter_derivative f D hD hf).mono inter_subset_right, ?_⟩
  intro q hq v
  let L := Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
  let K := FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (s q)
  let : IsMonHom K := FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_group S G k (s q)
  have hK : MDifferentiableAt (𝓘(ℝ, L)) (𝓘(ℝ, L)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K) 1 :=
    (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map K 1).mdifferentiableAt (by simp)
  have hK1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K 1 = 1 := MonObj.one_comp K
  have heq : (fun y => f (q, y)) =ᶠ[𝓝 (0 : E)]
      (fun y => c q (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K ((c q).symm y))) := by
    have hmem := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hD.mem_nhds hq.2)
    filter_upwards [hmem] with y hy
    have hyt : y ∈ (c q).target := by rw [(hc q hq.1).2.2.2.2.1]; exact htarget hy
    exact FiberEndomorphismCoordinates.Abelian.RelativeCharts.familyEndomorphismCoordinates_eq_fiber_chart G k i N (s q) q (c q)
      (hc q hq.1).2.2.2.1 (hc q hq.1).2.2.2.2.2.1 (hc q hq.1).2.2.2.2.2.2
      y hyt (himage _ hy)
  change ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L) (c q) (fderiv ℝ (fun y => f (q, y)) 0 v) = _
  rw [heq.fderiv_eq]
  exact ChartEndomorphismDerivative.Abelian.chartEndomorphism_derivative (c q) (hc q hq.1).2.2.1 (hc q hq.1).1 (hc q hq.1).2.1
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K) hK hK1 v

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyEndomorphismDerivative.Abelian.RelativeCharts
