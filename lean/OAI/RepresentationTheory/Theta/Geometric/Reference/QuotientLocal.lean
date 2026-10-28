import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliChart
import OAI.RepresentationTheory.Theta.Geometric.ArithmeticAmbientProjection

/-! # Quotient Local -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The unique arithmetic orbit of each original reference moduli point
defines exact quotient coordinates on a component exhausted by such points. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ D.pel.complexSpace)
    (href : ∀ x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ∃ a : D.domain, x ≫ f = D.referenceModuliMap hg a)

def Data.ActiveHeckeThetaData.referenceQuotientCoordinates (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : D.ArithmeticBallQuotient :=
  D.arithmeticBallProjection (Classical.choose (href x))

variable (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s)

theorem Data.ActiveHeckeThetaData.referenceQuotientCoordinates_moduli (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    D.arithmeticModuliMap hg hc hgood hdegree (D.referenceQuotientCoordinates hg f href x) = x ≫ f :=
  (Classical.choose_spec (href x)).symm

include hc hgood hdegree

theorem Data.ActiveHeckeThetaData.referenceQuotientCoordinates_eq_projection (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (a : D.domain)
    (ha : x ≫ f = D.referenceModuliMap hg a) :
    D.referenceQuotientCoordinates hg f href x = D.arithmeticBallProjection a := by
  apply D.arithmeticModuliMap_injective hg hc hgood hdegree
  rw [D.referenceQuotientCoordinates_moduli hg f href hc hgood hdegree, ha]
  rfl

theorem Data.ActiveHeckeThetaData.referenceQuotientCoordinates_injective [Mono f] :
    Function.Injective (D.referenceQuotientCoordinates hg f href) := by
  intro x y h
  apply (cancel_mono f).mp
  have he := congrArg (D.arithmeticModuliMap hg hc hgood hdegree) h
  simpa only [D.referenceQuotientCoordinates_moduli hg f href hc hgood hdegree] using he

theorem Data.ActiveHeckeThetaData.referenceQuotientCoordinates_chart
    (e : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (he : ∀ y ∈ e.source, ∃ hp : e y ∈ D.domain, y ≫ f = D.referenceModuliMap hg ⟨e y, hp⟩)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} (hx : x ∈ e.source) :
    D.referenceQuotientCoordinates hg f href x = D.arithmeticAmbientProjection hg (e x) := by
  obtain ⟨hp, hpoint⟩ := he x hx
  rw [D.referenceQuotientCoordinates_eq_projection hg f href hc hgood hdegree x ⟨e x, hp⟩ hpoint]
  exact (D.arithmeticAmbientProjection_coe hg ⟨e x, hp⟩).symm

end

section

/-! Exact quotient coordinates on an original reference surface are
locally holomorphic homeomorphisms for the actual arithmetic quotient atlas. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.pel.complexSpace) [Mono f]
    (href : ∀ x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ∃ a : D.domain, x ≫ f = D.referenceModuliMap hg a)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hdim : AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2)

include hs hdim in
theorem Data.ActiveHeckeThetaData.referenceQuotientCoordinates_local_charts :
    letI := D.arithmeticBallAtlas hg hc hgood hdegree
    ∀ x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S,
      ∃ e : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) D.ArithmeticBallQuotient,
        x ∈ e.source ∧
        e.MDifferentiable (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
          (𝓘(ℂ, LinearTheta.BallCoordinates)) ∧
        EqOn (D.referenceQuotientCoordinates hg f href) e e.source := by
  let : IsCancelSMul D.archimedeanArithmeticSubgroup D.domain := D.archimedeanArithmetic_free hg hc hgood hdegree
  let : ProperlyDiscontinuousSMul D.archimedeanArithmeticSubgroup D.domain :=
    D.archimedeanArithmetic_properlyDiscontinuous hg hc hgood hdegree
  let : ChartedSpace LinearTheta.BallCoordinates D.ArithmeticBallQuotient := D.arithmeticBallAtlas hg hc hgood hdegree
  let : IsManifold (𝓘(ℂ, LinearTheta.BallCoordinates)) 1 D.ArithmeticBallQuotient := D.arithmeticBallAtlas_isManifold hg hc hgood hdegree
  intro x
  obtain ⟨a, ha⟩ := href x
  obtain ⟨c, hxc, hca, hcd, _, hcm⟩ := D.exists_reference_moduli_chart hg f hs hdegree hdim x a ha
  let p := Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientChart _ hg.reference_admissible.2.2.2.1 D.archimedeanArithmeticSubgroup a
  have hp : p ∈ atlas LinearTheta.BallCoordinates D.ArithmeticBallQuotient := ⟨a, rfl⟩
  have hpd := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, LinearTheta.BallCoordinates)) hp
  have hat : a.val ∈ p.target := Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientChart_target_self _ hg.reference_admissible.2.2.2.1 _ a
  let e := c.trans p.symm
  refine ⟨e, ⟨hxc, ?_⟩, hcd.trans hpd.symm, ?_⟩
  · change c x ∈ p.target
    rwa [hca]
  · intro y hy
    have h := D.referenceQuotientCoordinates_chart hg f href hc hgood hdegree c hcm hy.1
    change D.referenceQuotientCoordinates hg f href y = p.symm (c y)
    exact h.trans (Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientChart_symm_apply _ hg.reference_admissible.2.2.2.1 _ a (c y)).symm

end

/-! Quotient coordinates are a local homeomorphism and are holomorphic
with bijective complex derivative everywhere on the actual surface. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set Filter
open scoped Classical _root_.Manifold _root_.Topology

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.pel.complexSpace) [Mono f]
    (href : ∀ x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ∃ a : D.domain, x ≫ f = D.referenceModuliMap hg a)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hdim : AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2)

include hc hgood hdegree hs hdim

theorem Data.ActiveHeckeThetaData.referenceQuotientCoordinates_localHomeomorph :
    IsLocalHomeomorph (D.referenceQuotientCoordinates hg f href) := by
  let := D.arithmeticBallAtlas hg hc hgood hdegree
  apply IsLocalHomeomorph.mk
  intro x
  obtain ⟨e, hx, _, he⟩ := D.referenceQuotientCoordinates_local_charts hg f href hc hgood hdegree hs hdim x
  exact ⟨e, hx, he⟩

theorem Data.ActiveHeckeThetaData.referenceQuotientCoordinates_derivative (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    letI := D.arithmeticBallAtlas hg hc hgood hdegree
    MDifferentiableAt (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
      (𝓘(ℂ, LinearTheta.BallCoordinates)) (D.referenceQuotientCoordinates hg f href) x ∧
      Function.Bijective (mfderiv (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
        (𝓘(ℂ, LinearTheta.BallCoordinates)) (D.referenceQuotientCoordinates hg f href) x) := by
  let := D.arithmeticBallAtlas hg hc hgood hdegree
  obtain ⟨e, hx, hed, he⟩ := D.referenceQuotientCoordinates_local_charts hg f href hc hgood hdegree hs hdim x
  have hevent : D.referenceQuotientCoordinates hg f href =ᶠ[𝓝 x] e :=
    Filter.mem_of_superset (e.open_source.mem_nhds hx) he
  refine ⟨hevent.mdifferentiableAt_iff.mpr (hed.mdifferentiableAt hx), ?_⟩
  rw [hevent.mfderiv_eq]
  exact hed.mfderiv_bijective hx

end

end OAI.RepresentationTheory.Theta.Geometric
