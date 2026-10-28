import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyChartData
import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodBases
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicPeriods
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicLocalPeriods
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicChartPeriodBases
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberCompactness
import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice
import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodBases
import OAI.ArithmeticGeometry.Descent.CMVariety.ClosedIdentitySection

/-! # Intrinsic Holomorphic Periods -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicPeriods.IntrinsicFamilyPeriods

noncomputable section

/-! Full integral period bases of the actual native abelian family
have holomorphic basis vectors throughout an open base neighborhood.
The original charts and complete actual exponential kernels are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set _root_.Metric
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj NNReal _root_.Topology

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F] [FiniteDimensional ℂ F]

/-- Construct full nearby integral period bases of the actual abelian family,
with continuous real coordinate maps. All central lattice data are constructed. -/
theorem exists_native_holomorphic_full_period_bases
    (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)
    (present : ∀ s : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback s.left))
    (V : (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)]
    [IsScalarTower ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)]
    (b : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G =
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)
        (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)) ≫ b)
    (σ : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V →ₐ[ℂ] R)
    (hσ : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V) R σ ≫
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV = b ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G)
    {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)}
    (N : ArithmeticGeometry.Descent.CMVariety.RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ) :
    let s := fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
      (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
    let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left := fun q => (present (s q)).isIntegral
    let L := fun q : F => Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (G.pullback (s q).left).scheme.hom) → ℂ
    let : ∀ q : F, T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
      fun q => (present (s q)).t2Space
    let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
      fun q => (present (s q)).nativeRealLieGroup
    let totalChart := ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V hV) N.charts.total
    ∃ (c : ∀ q : F, OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) E)
      (n : ℕ) (e : F → (Fin n → ℝ) ≃L[ℝ] E),
      ArithmeticGeometry.Descent.CMVariety.FamilyChartData.Abelian.FamilyIdentityChartData L
        (fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) c
        (fun q z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)
        totalChart N.neighborhood ∧
      ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian.LocalPeriodFamily (fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme)
        (fun q => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q))
        (fun q z => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z)
        (N.charts.base (x.comp
          (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V)))) ∧
      ∃ U : Set F, IsOpen U ∧
        N.charts.base (x.comp
          (IsScalarTower.toAlgHom ℂ R (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V))) ∈ U ∧
        ContinuousOn (fun q => (e q).toContinuousLinearMap) U ∧
        (∀ i, DifferentiableOn ℂ (fun q => e q (Pi.single i 1)) U) ∧
        ∀ q ∈ U, ∃ b : Module.Basis (Fin n) ℤ (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := L q) (c q)),
          ∀ i, (b i : E) = e q (Pi.single i 1) := by
  intro s hIntegral L hT2 hLie totalChart
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) V
  let H := fun q : F => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  obtain ⟨c₀, hc₀, hp₀, hcontinue⟩ := IntrinsicHolomorphicLocalPeriods.IntrinsicFamilyPeriods.exists_native_holomorphic_local_period_family G present V hV b hi σ hσ N
  let c : ∀ q : F, OpenPartialHomeomorph (H q) E := c₀
  have hc := hc₀
  let embed := fun q : F => fun z : H q =>
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (s q)) z
  have hp : ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian.LocalPeriodFamily H (fun q => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q)) embed q₀ := hp₀
  let : CompactSpace (H q₀) := (present (s q₀)).compactSpace
  let : ConnectedSpace (H q₀) := (present (s q₀)).connectedSpace
  let K := Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G))
  have hK : IsClosed K := ArithmeticGeometry.Descent.CMVariety.ClosedIdentitySection.Abelian.FamilyPoints.identitySection_native_closed S G
  have hmem (q : F) (v : E) :
      embed q (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v) ∈ K ↔
        ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q) v = 1 :=
    ArithmeticGeometry.Descent.CMVariety.ClosedIdentitySection.Abelian.FamilyPoints.fiberInclusion_mem_identitySection_iff S G (s q)
      (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (G := H q) (c q) v)
  obtain ⟨n, e, U, hU, hqU, he, hhol, hb⟩ := HolomorphicChartPeriodBases.exists_holomorphic_full_chart_period_bases_on L H q₀ c embed
    hp hcontinue (hc q₀ N.center).2.2.1 (hc q₀ N.center).1 (hc q₀ N.center).2.1 K hK hmem
  refine ⟨c, n, e, hc, hp, U, hU, hqU, he, ?_, ?_⟩
  · intro i
    apply (hhol i).congr
    intro q _
    apply congrArg (e q)
    funext j
    simp [Pi.single_apply]
  · intro q hq
    obtain ⟨bq, hbq⟩ := hb q hq
    refine ⟨bq, fun i => (hbq i).trans ?_⟩
    apply congrArg (e q)
    funext j
    simp [Pi.single_apply]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicPeriods.IntrinsicFamilyPeriods
