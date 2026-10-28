import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothRelativeNeighborhoods
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Regular Relative Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.RegularRelativeCharts.Abelian.RelativeCharts

noncomputable section

/-!
The smooth relative charts are actual regular-coordinate charts. Their
forward coordinates are fractions of regular functions, with a common
denominator nonzero throughout the chart source. This proves analytic
compatibility with the native regular atlas and analyticity of actual
algebra maps in these coordinates.
-/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
open scoped Classical ContDiff

section AnalyticCoordinates

variable {A E F : Type} [CommRing A] [Algebra ℂ A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedSpace ℂ E] in
theorem continuousOn_affinePoints_of_evaluations
    (f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (U : Set E)
    (hf : ∀ a : A, ContinuousOn (fun z => f z a) U) : ContinuousOn f U := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
  intro a
  exact (hf a).domRestrict

/-- Forward-chart analyticity tested on actual characters by evaluation
of regular functions. This property is proved for the constructed charts
and remains valid after analytic changes of coordinates. -/
def HasAnalyticCoordinates (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) E) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (U : Set V),
    (∀ a : A, ContDiffOn ℂ ω (fun z => f z a) U) →
      ContDiffOn ℂ ω (fun z => e (f z)) (U ∩ f ⁻¹' e.source)

theorem HasAnalyticCoordinates.trans
    {e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) E}
    (he : HasAnalyticCoordinates e) (t : OpenPartialHomeomorph E F)
    (ht : ContDiffOn ℂ ω t t.source) : HasAnalyticCoordinates (e.trans t) := by
  intro V _ _ f U hf
  exact ht.comp ((he V f U hf).mono (fun _ hz => ⟨hz.1, hz.2.1⟩))
    (fun _ hz => hz.2.2)

theorem HasAnalyticCoordinates.transHomeomorph
    {e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) E}
    (he : HasAnalyticCoordinates e) (t : E ≃L[ℂ] F) :
    HasAnalyticCoordinates (e.transHomeomorph t.toHomeomorph) := by
  intro V _ _ f U hf
  exact t.contDiff.comp_contDiffOn (he V f U hf)

end AnalyticCoordinates

variable {A : Type} [CommRing A] [Algebra ℂ A]
  {Index : Type} [Fintype Index]

/-- Forward coordinates are actual regular fractions on the chart source. -/
def HasRegularCoordinates
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Index → ℂ)) : Prop :=
  ∃ g : A, (∀ x ∈ e.source, x g ≠ 0) ∧
    ∀ i : Index, ∃ (a : A) (k : ℕ),
      ∀ x ∈ e.source, e x i = x a / (x g) ^ k

omit [Fintype Index] in
theorem hasRegularCoordinates_of_evaluation
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Index → ℂ))
    (v : Index → A) (hv : ∀ x i, e x i = x (v i)) :
    HasRegularCoordinates e := by
  refine ⟨1, ?_, ?_⟩
  · intro x _
    simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true]
  · intro i
    refine ⟨v i, 0, ?_⟩
    intro x _
    simpa only [pow_zero, div_one] using hv x i

omit [Fintype Index] in
/-- Lifting a polynomial-coordinate chart through the actual localization
open immersion yields the required regular fractions on the original algebra. -/
theorem localization_chart_hasRegularCoordinates
    (g : A)
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) (Index → ℂ))
    (v : Index → Localization.Away g) (hv : ∀ x i, e x i = x (v i)) :
    HasRegularCoordinates (e.lift_openEmbedding
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g)) := by
  let inc := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g
  have hi : Topology.IsOpenEmbedding inc :=
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g
  refine ⟨g, ?_, ?_⟩
  · rintro x ⟨y, _, rfl⟩
    exact (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g y).property
  · intro i
    refine ⟨(IsLocalization.Away.sec g (v i)).1,
      (IsLocalization.Away.sec g (v i)).2, ?_⟩
    rintro x ⟨y, _, rfl⟩
    change (e.lift_openEmbedding hi) (inc y) i = _
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, hv]
    exact AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts.localizedPoint_eval_eq_div g y (v i)

/-- Every regular-coordinate chart evaluates analytically on any family
of algebra characters whose regular-function evaluations are analytic.
The source model can itself be a product of base and fiber coordinates. -/
theorem HasRegularCoordinates.contDiffOn
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Index → ℂ)}
    (he : HasRegularCoordinates e) (f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (U : Set E)
    (hf : ∀ a : A, ContDiffOn ℂ ω (fun z => f z a) U) :
    ContDiffOn ℂ ω (fun z => e (f z)) (U ∩ f ⁻¹' e.source) := by
  obtain ⟨g, hg, hcoords⟩ := he
  apply contDiffOn_pi.mpr
  intro i
  obtain ⟨a, k, hcoord⟩ := hcoords i
  have heval (b : A) : ContDiffOn ℂ ω (fun z => f z b) (U ∩ f ⁻¹' e.source) :=
    (hf b).mono Set.inter_subset_left
  apply ((heval a).div ((heval g).pow k) (fun z hz =>
    pow_ne_zero k (hg (f z) hz.2))).congr
  intro z hz
  exact hcoord (f z) hz.2

theorem HasRegularCoordinates.comap_contDiffOn
    {B E : Type} [CommRing B] [Algebra ℂ B]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Index → ℂ)}
    (he : HasRegularCoordinates e) (h : A →ₐ[ℂ] B)
    (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) E)
    (hf : ∀ b : B, ContDiffOn ℂ ω (fun z => f.symm z b) f.target) :
    ContDiffOn ℂ ω (fun z => e ((f.symm z).comp h))
      (f.target ∩ {z | (f.symm z).comp h ∈ e.source}) :=
  he.contDiffOn (fun z => (f.symm z).comp h) f.target (fun a => hf (h a))

theorem HasRegularCoordinates.hasAnalyticCoordinates
    {e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Index → ℂ)}
    (he : HasRegularCoordinates e) : HasAnalyticCoordinates e := by
  intro V _ _ f U hf
  exact he.contDiffOn f U hf

/-- The constructed relative charts retain the explicit regular-coordinate
formulas on both the total space and the base. -/
theorem exists_relative_regular_charts
    {R I Sigma J Tau : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R A] [IsScalarTower ℂ R A]
    [Fintype I] [Fintype Sigma] [Fintype J] [Fintype Tau]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma) (g : A)
    (Q : Algebra.SubmersivePresentation R (Localization.Away g) J Tau)
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hg : x g ≠ 0) :
    ∃ C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (ComposedSmoothCharts.Abelian.RelativeCharts.baseProjection P Q),
      HasRegularCoordinates C.base ∧ HasRegularCoordinates C.total := by
  obtain ⟨eR, e₀, hxR, hx₀, hs, hp, hiA, hiR, hR, hA⟩ :=
    ComposedSmoothCharts.Abelian.RelativeCharts.exists_compatible_smooth_charts_with_coordinates P Q (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg)
  obtain ⟨eA, hb, hx, hsA, hpA, hi, heq⟩ :=
    SmoothRelativeNeighborhoods.Abelian.RelativeCharts.lift_relative_chart_with_eq x g hg eR e₀ (ComposedSmoothCharts.Abelian.RelativeCharts.baseProjection P Q) hxR hx₀ hs hp hiA
  refine ⟨⟨eR, eA, hb, hx, hsA, hpA, hi, hiR⟩, ?_, ?_⟩
  · exact hasRegularCoordinates_of_evaluation eR (fun i => P.val i.val) hR
  · change HasRegularCoordinates eA
    rw [heq]
    exact localization_chart_hasRegularCoordinates g e₀
      (fun i => (Q.comp P).val i.val) hA

/-- Smoothness alone supplies the relative presentation and compatible
regular charts. No analytic compatibility hypothesis is needed. -/
theorem exists_smooth_relative_regular_charts
    {R I Sigma : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R A] [IsScalarTower ℂ R A] [Fintype I] [Fintype Sigma]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    [Algebra.Smooth R A] (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ (D : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.RelativePresentationAt (R := R) x)
      (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (ComposedSmoothCharts.Abelian.RelativeCharts.baseProjection P D.presentation)),
      HasRegularCoordinates C.base ∧ HasRegularCoordinates C.total := by
  obtain ⟨D⟩ := SmoothRelativeNeighborhoods.Abelian.RelativeCharts.exists_relative_presentationAt (R := R) x
  obtain ⟨C, hb, ht⟩ := exists_relative_regular_charts P D.element D.presentation x D.nonzero
  exact ⟨D, C, hb, ht⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.RegularRelativeCharts.Abelian.RelativeCharts
