import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothSchemeFiberCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws

/-! # Section Fiber Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Use a section-normalized chart to construct differentiable charts on
every nearby literal abelian fiber. Their units have coordinate zero,
their domains are the slices of one fixed total-space chart, and their
inverse maps are restrictions of its actual native inverse.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj

section

variable {R A E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The same relative charts apply at every point in their source. -/
def SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.recenter {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A} {p : E → F}
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x p)
    (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hy : y ∈ C.total.source) :
    SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) y p where
  base := C.base
  total := C.total
  basePoint := by
    simpa only [C.total.left_inv hy] using C.mapsTo _ (C.total.map_source hy)
  point := hy
  mapsTo := C.mapsTo
  projection := C.projection
  regularTotal := C.regularTotal
  regularBase := C.regularBase

end

namespace SectionFiberCharts.Abelian.FamilyPoints

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Construct the chart on each actual nearby fiber, using the given
algebraic identity section and the constructed normalized total chart. -/
theorem exists_identity_fiber_chart
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (V : (AbelianFamilyPoints.FamilyPoints.total S G).left.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)]
    [IsScalarTower ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)]
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (hi : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV ≫ AbelianFamilyPoints.FamilyPoints.projection S G =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)
        (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)) ≫ b)
    (σ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V →ₐ[ℂ] R)
    (hσ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V) R σ ≫
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV = b ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G)
    {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)}
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ)
    (q : F) (hq : q ∈ N.neighborhood)
    [IsIntegral (G.pullback
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (N.charts.base.symm q)).left).scheme.left] :
    let s := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
    let e := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV) N.charts.total
    ∃ c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) E,
      (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) ∈ c.source ∧ c 1 = 0 ∧
      c.MDifferentiable
        (𝓘(ℝ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback s.left).scheme.hom) → ℂ))
        (𝓘(ℝ, E)) ∧
      c.source = (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)) ⁻¹' e.source ∧
      c.target = {v | (q, v) ∈ e.target} ∧
      (∀ z ∈ c.source, c z = (e (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) z)).2) ∧
      (∀ v ∈ c.target,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (c.symm v) = e.symm (q, v)) ∧
      ContMDiffOn
        (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback s.left).scheme.hom) → ℂ))
        (𝓘(ℂ, E)) ω c c.source ∧
      ContMDiffOn (𝓘(ℂ, E))
        (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback s.left).scheme.hom) → ℂ))
        ω c.symm c.target := by
  dsimp only
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV
  let s := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
  let xp := (N.charts.base.symm q).comp σ
  let p := AbelianFamilyPoints.FamilyPoints.projection S G
  let h := AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V
  let : IsIntegral (AbelianFamilyPoints.FamilyPoints.fiber p s).left :=
    inferInstanceAs (IsIntegral (G.pullback s.left).scheme.left)
  let : Smooth (AbelianFamilyPoints.FamilyPoints.fiber p s).hom :=
    inferInstanceAs (Smooth (G.pullback s.left).scheme.hom)
  have hidentity : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i xp = s ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G := by
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap σ (N.charts.base.symm q)) = _
    rw [← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap A (CommAlgCat.of ℂ R) σ i]
    rw [hσ]
    exact AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp (CommAlgCat.of ℂ R) b (AbelianFamilyPoints.FamilyPoints.identitySection S G) _
  have hrange : xp ∈ Set.range (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) := by
    rw [ClosedFiberAffine.Abelian.FamilyPoints.fiberAffinePullback_range]
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i xp) = s
    rw [hidentity]
    exact (AbelianFamilyPoints.FamilyPoints.native_identitySection S G).2 s
  obtain ⟨y₀, hy₀⟩ := hrange
  have hy : y₀.comp h ∈ N.charts.total.source := by
    change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h y₀ ∈ N.charts.total.source
    rw [hy₀]
    exact N.sectionPoint q hq
  let C := N.charts.recenter (y₀.comp h) hy
  have hcoord : C.base ((y₀.comp h).comp (IsScalarTower.toAlgHom ℂ R A)) = q := by
    have he := C.projection (C.total (y₀.comp h)) (C.total.map_source C.point)
    rw [C.total.left_inv C.point] at he
    change N.charts.base ((y₀.comp h).comp (IsScalarTower.toAlgHom ℂ R A)) =
      (N.charts.total (y₀.comp h)).1 at he
    change y₀.comp h = xp at hy₀
    rw [hy₀, N.sectionZero q hq] at he
    change N.charts.base ((y₀.comp h).comp (IsScalarTower.toAlgHom ℂ R A)) = q
    rw [hy₀]
    exact he
  obtain ⟨c, hc, hf, hmd, hs, ht, hinv, hcomplex, hcomplexInv⟩ :=
    SmoothSchemeFiberCharts.Abelian.FamilyPoints.exists_differentiable_schemeFiber_chart p s V hV b hi y₀ C N.forwardTotal
  have hunit : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap (AbelianFamilyPoints.FamilyPoints.fiber p s)
      ((AbelianFamilyPoints.FamilyPoints.fiberInclusion p s).left ⁻¹ᵁ V) (hV.preimage (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s).left) y₀ =
        (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) := by
    apply (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
      (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s)).injective
    rw [FiberGroupLaws.Abelian.FamilyPoints.fiberInclusion_one]
    exact (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) V hV
      (hV.preimage (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s).left) y₀).trans
        ((congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) hy₀).trans hidentity)
  have hc1 : (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) ∈ c.source := hunit ▸ hc
  have hc0 : c (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) = 0 := by
    have he := hf (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) hc1
    apply he.trans
    rw [FiberGroupLaws.Abelian.FamilyPoints.fiberInclusion_one, ← hidentity]
    change ((N.charts.total.lift_openEmbedding (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap A i))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i xp)).2 = 0
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, N.sectionZero q hq]
  refine ⟨c, hc1, hc0, hmd, hs, ?_, hf, ?_, hcomplex, hcomplexInv⟩
  · exact ht.trans (by rw [hcoord]; rfl)
  · intro v hv
    have he := hinv v hv
    rw [hcoord] at he
    exact he

end SectionFiberCharts.Abelian.FamilyPoints

end

end OAI.ArithmeticGeometry.Descent.CMVariety
