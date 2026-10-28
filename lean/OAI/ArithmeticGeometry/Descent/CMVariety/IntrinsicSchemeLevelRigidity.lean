import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicTorsionRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLevelPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.PresentedTorsionPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.PresentedLevel
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPresentedPeriods
import OAI.ArithmeticGeometry.Descent.CMVariety.PresentedDerivativeCoordinates
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyEndomorphismDerivative
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyRigidity

/-! # Intrinsic Scheme Level Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicSchemeLevelRigidity.Abelian.FamilyPoints

noncomputable section

/-!
Local equivariant CM rigidity preserving the full level on every test
scheme, for an actual abelian family in constructed algebraic charts. Full integral period bases, complex marked
period continuity, and endomorphism derivative continuity are all proved
from the actual family; none is an input to this theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff _root_.Manifold _root_.CategoryTheory.MonObj _root_.Topology

local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

/-- Retaining a constructed finite list of central CM endomorphisms
forces the actual nearby fibers to be algebraically group-isomorphic,
compatibly with those endomorphisms. -/
theorem native_scheme_family_locally_cm_rigid_with_level
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
    (N : RegularSectionCharts.Abelian.RelativeCharts.SectionNormalizedCharts (E := E) (F := F) x σ)
    (levelOrder : ℕ) (hlevelOrder : 0 < levelOrder) (level : G.FullLevel levelOrder) :
    let s := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap
      (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
    let q₀ := N.charts.base (x.comp
      (IsScalarTower.toAlgHom ℂ R (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V)))
    (present (s q₀)).variety.HasCMH1 →
    ∃ (r : ℕ) (m : Fin r → ((present (s q₀)).variety.toOver ⟶ (present (s q₀)).variety.toOver)),
      (∀ j, IsMonHom (m j)) ∧
      ∀ k : Fin r → (G.scheme ⟶ G.scheme),
        (∀ j, IsMonHom (k j)) →
        (∀ j, (present (s q₀)).comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k j) (s q₀) ≫
          (present (s q₀)).comparison.hom = m j) →
        ∀ᶠ q in 𝓝 q₀,
          ∃ e : (present (s q₀)).variety.toOver ≅ (present (s q)).variety.toOver,
            IsMonHom e.hom ∧ (∀ j,
              m j ≫ e.hom = e.hom ≫ (present (s q)).comparison.inv ≫
                FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k j) (s q) ≫ (present (s q)).comparison.hom) ∧
            StandardModuli.Abelian.ComplexAbelianPresentation.FullLevelCompatible (present (s q₀)) (present (s q))
              (level.pullback (s q₀).left) (level.pullback (s q).left) e := by
  dsimp only
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (AbelianFamilyPoints.FamilyPoints.total S G) V
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (AbelianFamilyPoints.FamilyPoints.total S G) V hV
  let s := fun q : F => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (N.charts.base.symm q)
  let q₀ := N.charts.base (x.comp (IsScalarTower.toAlgHom ℂ R A))
  intro hCM
  let : ∀ q : F, IsIntegral (G.pullback (s q).left).scheme.left := fun q => (present (s q)).isIntegral
  let : ∀ q : F, T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
    fun q => (present (s q)).t2Space
  let L := fun q : F => ContinuousPresentedPeriods.Abelian.abelianSchemeNativeModel (G.pullback (s q).left)
  let : ∀ q : F, LieGroup (𝓘(ℝ, L q)) ∞ (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q).left).scheme) :=
    fun q => (present (s q)).nativeRealLieGroup
  obtain ⟨c, n, r, hc, hperiodFamily, hr, hb⟩ := IntrinsicPeriods.Abelian.FamilyPoints.exists_native_full_period_bases G present V hV b hi σ hσ N
  let : ConnectedSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (s q₀).left).scheme) :=
    (present (s q₀)).connectedSpace
  have hsurj := ChartTorsionReferences.Abelian.chartExponential_surjective (E := L q₀) (c q₀)
    (hc q₀ N.center).2.2.1 (hc q₀ N.center).1 (hc q₀ N.center).2.1
  obtain ⟨levelCoordinates, hlevelCoordinates⟩ := FamilyLevelPeriods.Abelian.FamilyPoints.exists_family_level_period_coordinates G s q₀
    (fun q => ChartEndomorphismDerivative.Abelian.chartExponential (E := L q) (c q)) hperiodFamily hsurj
    (fun q => ChartPeriodLattice.Abelian.chartPeriodLattice (E := L q) (c q))
    (fun q => ChartPeriodLattice.Abelian.mem_chartPeriodLattice (E := L q) (c q))
    (fun q => (r q).toContinuousLinearMap) hr (by
      filter_upwards [hb] with q hq
      obtain ⟨bq, hbq⟩ := hq
      refine ⟨bq, fun j => (hbq j).trans ?_⟩
      apply congrArg (r q)
      funext k
      simp [Pi.single_apply]) levelOrder hlevelOrder level
    (IntrinsicTorsionRigidity.Abelian.FamilyPoints.native_torsion_section_locally_one G present V hV b hi σ hσ N levelOrder hlevelOrder)
  have hnb : N.neighborhood ∩ {q : F | ∃ bq : Module.Basis (Fin n) ℤ
      (ChartPeriodLattice.Abelian.chartPeriodLattice (E := L q) (c q)), ∀ j, (bq j : E) = r q (Pi.single j 1)} ∈ 𝓝 q₀ :=
    Filter.inter_mem (N.isOpen.mem_nhds N.center) hb
  obtain ⟨U, hUsub, hUopen, hU₀⟩ := mem_nhds_iff.mp hnb
  let p₀ : U := ⟨q₀, hU₀⟩
  let fiberA := fun q : U => G.pullback (s q.val).left
  let P := fun q : U => present (s q.val)
  have hc' (q : U) : (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (fiberA q).scheme) ∈ (c q.val).source ∧
      c q.val 1 = 0 ∧
      ContMDiffOn (𝓘(ℂ, L q.val)) (𝓘(ℂ, E)) 1 (c q.val) (c q.val).source ∧
      ContMDiffOn (𝓘(ℂ, E)) (𝓘(ℂ, L q.val)) 1 (c q.val).symm (c q.val).target := by
    obtain ⟨h1, h0, _, _, _, _, _, hf, hi'⟩ := hc q.val (hUsub q.property).1
    exact ⟨h1, h0, hf.of_le (by simp), hi'.of_le (by simp)⟩
  have hr' : ContinuousAt (fun q : U => (r q.val).toContinuousLinearMap) p₀ :=
    ContinuousAt.comp (f := fun q : U => q.val) (x := p₀) hr continuous_subtype_val.continuousAt
  obtain ⟨d, e, T, marking, hT, hmarking, hperiod⟩ := ContinuousPresentedPeriods.Abelian.exists_continuous_presented_periods
    fiberA P (fun q : U => c q.val) hc' n (fun q : U => r q.val)
    (fun q => (hUsub q.property).2) p₀ hr'
  let levelVectors := fun a : Multiplicative (Fin (2 * g) → ZMod levelOrder) =>
    fun i : Fin n => (((levelOrder : ℝ)⁻¹ * (levelCoordinates a i : ℝ) : ℝ) : ℂ)
  have hlevelCoordinatesU : ∀ᶠ q : U in 𝓝 p₀, ∀ a,
      ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.val) (c q.val)
        ((levelOrder : ℝ)⁻¹ • r q.val (fun i => (levelCoordinates a i : ℝ))) =
      ((level.pullback (s q.val).left).hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
        (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val :=
    (continuous_subtype_val.continuousAt (x := p₀)).eventually hlevelCoordinates
  have hmarkedLevel : ∀ᶠ q : U in 𝓝 p₀,
      StandardModuli.Abelian.ComplexAbelianPresentation.MarkedLevelReferences (P q)
        (level.pullback (s q.val).left) (marking q) levelVectors := by
    filter_upwards [hlevelCoordinatesU] with q hq
    intro a
    have h := (P q).chart_divided_period_eq_marked (c q.val) (T q) (hT q)
      (marking q) (r q.val).toLinearMap (by
        intro j
        apply (hmarking q j).trans
        apply congrArg (T q)
        apply congrArg (r q.val)
        funext k
        simp [Pi.single_apply]) levelOrder (levelCoordinates a)
    exact (congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P q).comparison.hom) (hq a)).symm.trans h
  let coord := fun q : U => ((T q).symm.trans e).toLinearEquiv
  obtain ⟨mcount, m, hm, hrigid⟩ := IntrinsicFamilyRigidity.Abelian.IntrinsicPeriods.continuous_native_periods_and_derivatives_locally_rigid
    (fun q : U => (P q).variety) marking d coord p₀ hperiod hCM
  refine ⟨mcount, m, hm, ?_⟩
  intro k hk hk₀
  let (j : Fin mcount) : IsMonHom (k j) := hk j
  let K := fun (q : U) (j : Fin mcount) =>
    (P q).comparison.inv ≫ FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k j) (s q.val) ≫ (P q).comparison.hom
  have hK (q : U) (j : Fin mcount) : IsMonHom (K q j) := by
    let : IsMonHom (P q).comparison.hom := (P q).comparison_group
    let : IsMonHom (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k j) (s q.val)) :=
      FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_group S G (k j) (s q.val)
    dsimp only [K]
    infer_instance
  have hx : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ≫ AbelianFamilyPoints.FamilyPoints.projection S G) ≫ AbelianFamilyPoints.FamilyPoints.identitySection S G := by
    have he := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap A (CommAlgCat.of ℂ R) σ i
      (x.comp (IsScalarTower.toAlgHom ℂ R A))
    have hxσ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap σ (x.comp (IsScalarTower.toAlgHom ℂ R A)) = x := N.onSection
    rw [hσ, hxσ, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp] at he
    have hp := FiberChartProjection.Abelian.RelativeCharts.nativeAffinePoint_base (AbelianFamilyPoints.FamilyPoints.projection S G) b i hi x
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ≫ AbelianFamilyPoints.FamilyPoints.projection S G = _ at hp
    rw [hp]
    exact he.symm
  have hderiv (j : Fin mcount) (l : Fin n) : ContinuousAt
      (fun q : U => coord q
        (mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P q).variety)) (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P q).variety))
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (K q j)) 1 (marking q l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P q).variety))) p₀ := by
    obtain ⟨B, D, hB, hB₀, _, hD, hDc⟩ :=
      IntrinsicFamilyEndomorphismDerivative.Abelian.RelativeCharts.exists_continuous_native_familyEndomorphism_derivative G (k j) i N hx s c (by
        intro q hq
        obtain ⟨h1, h0, hmd, hsrc, htgt, hf, hi', _, _⟩ := hc q hq
        exact ⟨h1, h0, hmd, hsrc, htgt, hf, hi'⟩)
    have hD' : ContinuousAt (fun q : U => D q.val) p₀ :=
      ContinuousAt.comp (f := fun q : U => q.val) (x := p₀)
        (hD.continuousAt (hB.mem_nhds hB₀)) continuous_subtype_val.continuousAt
    have hDc' : ∀ᶠ q : U in 𝓝 p₀, ∀ v,
        ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L q.val) (c q.val) (D q.val v) =
          mfderiv (𝓘(ℝ, L q.val)) (𝓘(ℝ, L q.val))
            (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k j) (s q.val))) 1
            (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := L q.val) (c q.val) v) := by
      have hev : ∀ᶠ q : U in 𝓝 p₀, q.val ∈ B :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds (hB.mem_nhds hB₀)
      exact hev.mono (fun q hq => hDc q.val hq)
    have h := PresentedDerivativeCoordinates.Abelian.continuousAt_presented_derivative_on_vectors fiberA P (fun q : U => c q.val) T hT
      (fun q : U => FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G (k j) (s q.val))
      (fun q => FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_group S G (k j) (s q.val))
      (fun q : U => D q.val) (fun q : U => r q.val (Pi.single l 1)) p₀ hD'
      (hr'.clm_apply continuousAt_const) hDc' d e
    convert h using 1
    funext q
    change e ((T q).symm (mfderiv (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P q).variety))
      (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P q).variety)) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (K q j)) 1
      (marking q l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P q).variety))) = _
    rw [hmarking]
  have hevent := hrigid K hK hk₀ hderiv
  change ∀ᶠ q in 𝓝 (p₀.val), _
  rw [← hUopen.isOpenEmbedding_subtypeVal.map_nhds_eq p₀]
  change ∀ᶠ q : U in 𝓝 p₀, _
  filter_upwards [hevent, hmarkedLevel] with q hq hlevelq
  obtain ⟨a, ha, hmarked, he⟩ := hq
  let : IsMonHom a.hom := ha
  refine ⟨a, ha, he, ?_⟩
  exact StandardModuli.Abelian.ComplexAbelianPresentation.fullLevelCompatible_of_marked_references (P p₀) (P q)
    (level.pullback (s p₀.val).left) (level.pullback (s q.val).left)
    (marking p₀) (marking q) levelVectors hmarkedLevel.self_of_nhds hlevelq a hmarked

end

end OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicSchemeLevelRigidity.Abelian.FamilyPoints
