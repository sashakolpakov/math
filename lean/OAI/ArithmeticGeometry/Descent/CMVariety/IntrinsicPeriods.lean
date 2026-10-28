import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyChartData
import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodBases
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicLocalPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberCompactness
import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice
import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodBases
import OAI.ArithmeticGeometry.Descent.CMVariety.ClosedIdentitySection

/-! # Intrinsic Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicPeriods.Abelian.FamilyPoints

noncomputable section

/-!
Full period-basis construction for the actual native abelian-scheme fibers,
using their genuine exponentials and the constructed relative charts.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal _root_.Topology

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

/-- Construct full nearby integral period bases of the actual abelian family,
with continuous real coordinate maps. All central lattice data are constructed. -/
theorem exists_native_full_period_bases
    (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
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
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ) :
    let s := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
      (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
    let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left := fun q => (present (s q)).isIntegral
    let L := fun q : F => Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
    let : ∀ q : F, T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
      fun q => (present (s q)).t2Space
    let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
      fun q => (present (s q)).nativeRealLieGroup
    let totalChart := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV) N.charts.total
    ∃ (c : ∀ q : F, OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) E)
      (n : ℕ) (e : F → (Fin n → ℝ) ≃L[ℝ] E),
      FamilyChartData.Abelian.FamilyIdentityChartData L
        (fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) c
        (fun q z => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)
        totalChart N.neighborhood ∧
      LocalPeriod.Abelian.LocalPeriodFamily (fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme)
        (fun q => ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q))
        (fun q z => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)
        (N.charts.base (x.comp
          (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)))) ∧
      ContinuousAt (fun q => (e q).toContinuousLinearMap)
        (N.charts.base (x.comp
          (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)))) ∧
      ∀ᶠ q in 𝓝 (N.charts.base (x.comp
          (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)))),
        ∃ b : Module.Basis (Fin n) ℤ (ChartPeriodLattice.Abelian.chartPeriodLattice (E := L q) (c q)),
          ∀ i, (b i : E) = e q (Pi.single i 1) := by
  dsimp only
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V
  let s := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
  let H := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme
  let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left := fun q => (present (s q)).isIntegral
  let L := fun q : F => Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
  let : ∀ q : F, T2Space (H q) := fun q => (present (s q)).t2Space
  let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (H q) := fun q => (present (s q)).nativeRealLieGroup
  let totalChart := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart A
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV) N.charts.total
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  obtain ⟨c₀, hc₀, hp₀⟩ := IntrinsicLocalPeriods.Abelian.FamilyPoints.exists_native_local_period_family G present V hV b hi σ hσ N
  let c : ∀ q : F, OpenPartialHomeomorph (H q) E := c₀
  have hc := hc₀
  let embed := fun q : F => fun z : H q =>
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z
  have hp : LocalPeriod.Abelian.LocalPeriodFamily H (fun q => ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q)) embed q₀ := hp₀
  let : CompactSpace (H q₀) := (present (s q₀)).compactSpace
  let : ConnectedSpace (H q₀) := (present (s q₀)).connectedSpace
  let K := Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.identitySection S G))
  have hK : IsClosed K := ClosedIdentitySection.Abelian.FamilyPoints.identitySection_native_closed S G
  have hmem (q : F) (v : E) :
      embed q (ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v) ∈ K ↔
        ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v = 1 :=
    ClosedIdentitySection.Abelian.FamilyPoints.fiberInclusion_mem_identitySection_iff S G (s q)
      (ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (G := H q) (c q) v)
  obtain ⟨n, e, he, hb⟩ := hp.exists_full_chart_period_bases L H q₀ c embed
    (hc q₀ N.center).2.2.1 (hc q₀ N.center).1 (hc q₀ N.center).2.1 K hK hmem
  exact ⟨c, n, e, hc, hp, he, hb⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicPeriods.Abelian.FamilyPoints
