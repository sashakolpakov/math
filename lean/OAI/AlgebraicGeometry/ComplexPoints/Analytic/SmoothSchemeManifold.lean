import OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.PresentationDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Smooth Scheme Manifold -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

noncomputable section

/-!
# Analytic compatibility of native smooth-scheme coordinate charts

This file works with actual complex algebra characters, equipped with their
ordinary evaluation topology. Its transition lemmas apply to charts obtained
from localized submersive presentations: inverse charts have analytic regular
function evaluations, and forward coordinates are genuine localization ratios.
No compatibility or dimension hypothesis is packaged as a substitute manifold.
-/

open scoped ContDiff _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A localized regular function is analytic in any chart in which regular
functions have analytic evaluations, on its actual nonvanishing locus. -/
theorem contDiffOn_affineEvaluationRatio
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (ι → ℂ))
    (hinv : ∀ a : A, ContDiffOn ℂ ω (fun z => e.symm z a) e.target)
    (a g : A) (k : ℕ) :
    ContDiffOn ℂ ω (fun z => e.symm z a / (e.symm z g) ^ k)
      (e.target ∩ {z | e.symm z g ≠ 0}) := by
  apply ((hinv a).mono Set.inter_subset_left).div
    (((hinv g).mono Set.inter_subset_left).pow k)
  intro z hz
  exact pow_ne_zero k hz.2

/-- The transition between two actual affine-character charts is analytic if
the first has analytic regular-function evaluations and the second's forward
coordinates are the ratios of regular functions supplied by its localization.
The denominator condition is required only on the second chart's source. -/
theorem contDiffOn_affineChartTransition
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (ι → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (κ → ℂ))
    (hinv : ∀ a : A, ContDiffOn ℂ ω (fun z => e.symm z a) e.target)
    (g : A) (hg : ∀ x ∈ f.source, x g ≠ 0)
    (hcoords : ∀ i : κ, ∃ (a : A) (k : ℕ),
      ∀ x ∈ f.source, f x i = x a / (x g) ^ k) :
    ContDiffOn ℂ ω (e.symm.trans f) (e.symm.trans f).source := by
  apply contDiffOn_pi.mpr
  intro i
  obtain ⟨a, k, hcoord⟩ := hcoords i
  have heval (b : A) : ContDiffOn ℂ ω (fun z => e.symm z b)
      (e.symm.trans f).source :=
    (hinv b).mono (fun _ hz => hz.1)
  apply ((heval a).div ((heval g).pow k) (fun z hz =>
    pow_ne_zero k (hg (e.symm z) hz.2))).congr
  intro z hz
  exact hcoord (e.symm z) hz.2

/-- The same actual transition is smooth over the reals, as required for real
smooth differential forms with complex coefficients. -/
theorem real_contDiffOn_affineChartTransition
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (ι → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (κ → ℂ))
    (hinv : ∀ a : A, ContDiffOn ℂ ω (fun z => e.symm z a) e.target)
    (g : A) (hg : ∀ x ∈ f.source, x g ≠ 0)
    (hcoords : ∀ i : κ, ∃ (a : A) (k : ℕ),
      ∀ x ∈ f.source, f x i = x a / (x g) ^ k) :
    ContDiffOn ℝ ω (e.symm.trans f) (e.symm.trans f).source :=
  (contDiffOn_affineChartTransition e f hinv g hg hcoords).restrict_scalars ℝ

/-- Concrete coordinate charts on affine algebra characters: every regular
function is analytic in the inverse chart, and every forward coordinate is
a localization ratio with a denominator nonzero on the chart source.

This is an explicit set of actual open partial homeomorphisms. Coverage must
be proved from algebraic smoothness before it can define a manifold atlas. -/
def affineRegularAtlas (A : Type*) [CommRing A] [Algebra ℂ A] (n : ℕ) :
    Set (OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ)) :=
  {e | (∀ a : A, ContDiffOn ℂ ω (fun z => e.symm z a) e.target) ∧
    ∃ g : A, (∀ x ∈ e.source, x g ≠ 0) ∧
      ∀ i : Fin n, ∃ (a : A) (k : ℕ),
        ∀ x ∈ e.source, e x i = x a / (x g) ^ k}

/-- Compatibility of the explicitly defined affine regular-coordinate atlas
is a theorem of calculus and the displayed localization formulas. -/
theorem affineRegularAtlas_compatible {n : ℕ}
    (e f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ affineRegularAtlas A n) (hf : f ∈ affineRegularAtlas A n) :
    ContDiffOn ℂ ω (e.symm.trans f) (e.symm.trans f).source := by
  obtain ⟨g, hg, hcoords⟩ := hf.2
  exact contDiffOn_affineChartTransition e f he.1 g hg hcoords

/-- Pullback by a genuine algebra homomorphism is analytic in any two of the
concrete regular-coordinate charts, on the actual chart-overlap domain. -/
theorem contDiffOn_affineChartComapTransition
    {B : Type*} [CommRing B] [Algebra ℂ B] (h : A →ₐ[ℂ] B)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (ι → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (κ → ℂ))
    (hinv : ∀ b : B, ContDiffOn ℂ ω (fun z => e.symm z b) e.target)
    (g : A) (hg : ∀ x ∈ f.source, x g ≠ 0)
    (hcoords : ∀ i : κ, ∃ (a : A) (k : ℕ),
      ∀ x ∈ f.source, f x i = x a / (x g) ^ k) :
    ContDiffOn ℂ ω (fun z => f ((e.symm z).comp h))
      (e.target ∩ {z | (e.symm z).comp h ∈ f.source}) := by
  apply contDiffOn_pi.mpr
  intro i
  obtain ⟨a, k, hcoord⟩ := hcoords i
  have heval (b : B) : ContDiffOn ℂ ω (fun z => e.symm z b)
      (e.target ∩ {z | (e.symm z).comp h ∈ f.source}) :=
    (hinv b).mono Set.inter_subset_left
  apply ((heval (h a)).div ((heval (h g)).pow k) (fun z hz =>
    pow_ne_zero k (hg ((e.symm z).comp h) hz.2))).congr
  intro z hz
  exact hcoord ((e.symm z).comp h) hz.2

section NativeSchemeCharts

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- A genuine affine open immersion gives an open embedding from ordinary
algebra characters into the native complex-point space of the scheme. -/
theorem isOpenEmbedding_affinePointMap (B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left] :
    Topology.IsOpenEmbedding (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion i).comp
    (SchemePointHomeomorphs.affineSchemePointHomeomorph B).isOpenEmbedding

/-- Lift an actual affine algebra chart through its genuine affine open
immersion to a chart on native scheme-valued complex points. -/
def affineChartOnScheme (B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left] {n : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ)) :
    OpenPartialHomeomorph (SchemePointHomeomorphs.schemeComplexPoints X) (Fin n → ℂ) :=
  e.lift_openEmbedding (isOpenEmbedding_affinePointMap B i)

@[simp]
theorem affineChartOnScheme_source (B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left] {n : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ)) :
    (affineChartOnScheme B i e).source =
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i '' e.source := rfl

@[simp]
theorem affineChartOnScheme_symm_apply (B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left] {n : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ)) (z : Fin n → ℂ) :
    (affineChartOnScheme B i e).symm z =
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i (e.symm z) := rfl

@[simp]
theorem affineChartOnScheme_apply (B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X) [IsOpenImmersion i.left] {n : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    affineChartOnScheme B i e (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i x) = e x :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _

end NativeSchemeCharts

variable [IsDomain A] [Algebra.Smooth ℂ A]

/-- At every point of a smooth integral complex algebra, the concrete regular
coordinate atlas contains a chart of the common dimension. This dimension is
the proved generic Kähler differential rank, not an additional input. -/
theorem exists_smoothDomain_affineRegularChart (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
        (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ),
      e ∈ affineRegularAtlas A (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) ∧ x ∈ e.source := by
  classical
  obtain ⟨g, hg, n, m, P, e, hx, hsource, hcoords, hinverse⟩ :=
    SmoothAffineCharts.exists_smoothAffinePoint_localChart x
  have hgne : g ≠ 0 := by
    intro h
    apply hg
    simp [h]
  let : IsDomain (Localization.Away g) := Localization.Away.isDomain hgne
  have hdim : Nat.card (JacobianRegularity.FreeCoordinates P.map) =
      Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A := by
    simpa only [Fintype.card_eq_nat_card] using
      (Foundations.Scheme.PresentationDimension.Algebraic.card_free_variables_eq_dimension P.toPreSubmersivePresentation).trans
        (Foundations.Scheme.SmoothDomainDimension.Algebraic.localized_submersive_dimension (R := ℂ) (S := A) (Submonoid.powers g) P)
  have hex : ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
        (Fin (Fintype.card (JacobianRegularity.FreeCoordinates P.map)) → ℂ),
      e ∈ affineRegularAtlas A (Fintype.card (JacobianRegularity.FreeCoordinates P.map)) ∧ x ∈ e.source := by
    refine ⟨e, ⟨hinverse, ⟨g, ?_, hcoords⟩⟩, hx⟩
    intro y hy
    exact hsource hy
  have hdim' : Fintype.card (JacobianRegularity.FreeCoordinates P.map) =
      Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A := Fintype.card_eq_nat_card.trans hdim
  exact (congrArg (fun d => ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (Fin d → ℂ), e ∈ affineRegularAtlas A d ∧ x ∈ e.source) hdim').mp hex

/-- The genuine smooth affine point manifold uses the concrete regular atlas,
whose coverage and common dimension were proved from algebraic smoothness. -/
instance smoothDomainChartedSpace :
    ChartedSpace (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) where
  atlas := affineRegularAtlas A (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A)
  chartAt x := Classical.choose (exists_smoothDomain_affineRegularChart x)
  mem_chart_source x := (Classical.choose_spec (exists_smoothDomain_affineRegularChart x)).2
  chart_mem_atlas x := (Classical.choose_spec (exists_smoothDomain_affineRegularChart x)).1

/-- The complex points of a smooth integral complex algebra form an actual
complex analytic manifold in their ordinary evaluation topology. -/
instance smoothDomainComplexIsManifold (r : ℕ∞ω) :
    IsManifold (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)) r
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := by
  apply isManifold_of_contDiffOn
    (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)) r _
  intro e f he hf
  have h := (affineRegularAtlas_compatible e f he hf).of_le (show r ≤ ω from le_top)
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using h

/-- The same genuine smooth affine manifold, with scalars restricted to the
reals, supplies the underlying manifold for differential forms. -/
instance smoothDomainRealIsManifold (r : ℕ∞ω) :
    IsManifold (𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)) r
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := by
  apply isManifold_of_contDiffOn
    (𝓘(ℝ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)) r _
  intro e f he hf
  have h := ((affineRegularAtlas_compatible e f he hf).of_le
    (show r ≤ ω from le_top)).restrict_scalars ℝ
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using h

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
