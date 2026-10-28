import OAI.AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalGraphChart
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PresentedPointTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalizationPointTopology
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # Smooth Affine Charts -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts

noncomputable section

/-!
# Local analytic charts on the genuine points of smooth complex algebras

Native presentations and principal localization identify actual algebra points
with actual polynomial zero sets. The selected Jacobian minor supplies analytic
regularity, so the chart existence statements have no extra derivative hypothesis.
The number of free coordinates is recorded locally; no constant dimension is assumed.
-/

open scoped Classical ContDiff _root_.Topology

section Presentation

variable {S ι σ : Type*} [CommRing S] [Algebra ℂ S] [Fintype ι] [Fintype σ]
  [DecidableEq ι]

/-- The actual selected/free linear coordinate change carries the equations of
an algebra presentation to the split polynomial zero set. -/
def presentationSplitZeroHomeomorph (P : Algebra.PreSubmersivePresentation ℂ S ι σ) :
    {z : ι → ℂ // ∀ j, MvPolynomial.eval z (P.relation j) = 0} ≃ₜ
      {z | PolynomialImplicit.splitPolynomialMap (JacobianRegularity.presentationSplitPolynomials P) z = 0} :=
  (JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).toHomeomorph.subtype (by
    intro v
    have h (j : σ) :
        PolynomialImplicit.splitPolynomialMap (JacobianRegularity.presentationSplitPolynomials P)
          (JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj v) j =
            MvPolynomial.eval v (P.relation j) :=
      JacobianRegularity.selectedPolynomialFamily_eval P.map P.map_inj P.relation v j
    constructor
    · intro hv
      funext j
      exact (h j).trans (hv j)
    · intro hv j
      exact (h j).symm.trans (congr_fun hv j))

/-- The point space of the actual presented algebra in selected/free coordinates. -/
def presentedSplitPointsHomeomorph (P : Algebra.PreSubmersivePresentation ℂ S ι σ) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints S ≃ₜ
      {z | PolynomialImplicit.splitPolynomialMap (JacobianRegularity.presentationSplitPolynomials P) z = 0} :=
  (PresentedPointTopology.presentedComplexPointsHomeomorph P.toPresentation).trans
    (presentationSplitZeroHomeomorph P)

omit [Fintype σ] [DecidableEq ι] in
@[simp]
theorem presentedSplitPointsHomeomorph_apply
    (P : Algebra.PreSubmersivePresentation ℂ S ι σ) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    (presentedSplitPointsHomeomorph P x).val = JacobianRegularity.presentationSplitPoint P x := by
  change JacobianRegularity.splitCoordinates P.map (PresentedPointTopology.presentedComplexPointsHomeomorph P.toPresentation x).val =
    JacobianRegularity.splitCoordinates P.map (fun i => x (P.val i))
  congr 1
  funext i
  exact PresentedPointTopology.presentedComplexPointsHomeomorph_apply P.toPresentation x i

omit [Fintype σ] [DecidableEq ι] in
@[simp]
theorem presentedSplitPointsHomeomorph_symm_apply
    (P : Algebra.PreSubmersivePresentation ℂ S ι σ)
    (z : {z | PolynomialImplicit.splitPolynomialMap (JacobianRegularity.presentationSplitPolynomials P) z = 0}) (a : S) :
    (presentedSplitPointsHomeomorph P).symm z a =
      MvPolynomial.eval ((JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).symm z.val)
        (P.σ a) := by
  change (PresentedPointTopology.presentedComplexPointsHomeomorph P.toPresentation).symm
    ((presentationSplitZeroHomeomorph P).symm z) a = _
  rw [PresentedPointTopology.presentedComplexPointsHomeomorph_symm_apply]
  rfl

/-- A native standard-smooth presentation gives local analytic coordinates on
its actual algebra points. Regular functions are analytic in the inverse chart. -/
theorem exists_standardSmooth_point_chart
    (P : Algebra.SubmersivePresentation ℂ S ι σ) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (JacobianRegularity.FreeCoordinates P.map → ℂ),
      x ∈ e.source ∧
      (∀ y i, e y i = y (P.val i.val)) ∧
      (∀ a : S, ContDiffOn ℂ ω (fun z => e.symm z a) e.target) := by
  let Q := JacobianRegularity.presentationSplitPolynomials P.toPreSubmersivePresentation
  let u := JacobianRegularity.presentationSplitPoint P.toPreSubmersivePresentation x
  have hu : PolynomialImplicit.splitPolynomialMap Q u = 0 :=
    JacobianRegularity.presentationSplitPoint_zero P.toPreSubmersivePresentation x
  obtain ⟨e₀, hx₀, hforward, hinverse⟩ := LocalGraphChart.exists_polynomial_zero_chart Q u hu
    (JacobianRegularity.standardSmooth_partialDerivative_isInvertible P x)
  let h := presentedSplitPointsHomeomorph P.toPreSubmersivePresentation
  let e := h.transOpenPartialHomeomorph e₀
  have hhx : h x = ⟨u, hu⟩ := by
    apply Subtype.ext
    exact presentedSplitPointsHomeomorph_apply P.toPreSubmersivePresentation x
  refine ⟨e, ?_, ?_, ?_⟩
  · change h x ∈ e₀.source
    rwa [hhx]
  · intro y i
    change e₀ (h y) i = y (P.val i.val)
    rw [hforward]
    change (h y).val.1 i = _
    rw [show (h y).val = JacobianRegularity.presentationSplitPoint P.toPreSubmersivePresentation y from
      presentedSplitPointsHomeomorph_apply P.toPreSubmersivePresentation y]
    rfl
  · intro a
    have hcoordinates : ContDiffOn ℂ ω
        (fun z => (JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).symm (e₀.symm z).val)
        e₀.target :=
      (JacobianRegularity.selectedCoordinateEquiv P.map P.map_inj).symm.contDiff.comp_contDiffOn hinverse
    have heval := (PolynomialImplicit.contDiff_polynomial_eval (P.σ a) ω).comp_contDiffOn hcoordinates
    change ContDiffOn ℂ ω (fun z => h.symm (e₀.symm z) a) e₀.target
    apply heval.congr
    intro z hz
    exact presentedSplitPointsHomeomorph_symm_apply P.toPreSubmersivePresentation
      (e₀.symm z) a

end Presentation

variable {S : Type*} [CommRing S] [Algebra ℂ S]

/-- Evaluation of an arbitrary character of a principal localization is an
actual fraction in the restricted character's evaluations. -/
theorem localizedPoint_eval_eq_div (g : S)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) (b : Localization.Away g) :
    y b = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g y
        (IsLocalization.Away.sec g b).1 /
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g y g) ^
        (IsLocalization.Away.sec g b).2 := by
  simp only [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction_apply]
  have hg : y (algebraMap S (Localization.Away g) g) ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map y).ne_zero
  apply (eq_div_iff (pow_ne_zero _ hg)).mpr
  have h := congrArg y (IsLocalization.Away.sec_spec (S := Localization.Away g) g b)
  simpa only [map_mul, map_pow] using h

/-- Every point of a smooth complex algebra has an actual local chart. Its
dimension is the number of free coordinates in a proved standard-smooth
principal neighborhood and is allowed to depend on the point. Forward chart
coordinates are regular fractions, and all regular functions are analytic
in the inverse chart. -/
theorem exists_smoothAffinePoint_localChart [Algebra.Smooth ℂ S]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) :
    ∃ (g : S) (_hg : x g ≠ 0) (n m : ℕ)
      (P : Algebra.SubmersivePresentation ℂ (Localization.Away g) (Fin n) (Fin m)),
      ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
          (Fin (Fintype.card (JacobianRegularity.FreeCoordinates P.map)) → ℂ),
        x ∈ e.source ∧
        e.source ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g ∧
        (∀ i, ∃ (a : S) (k : ℕ), ∀ y ∈ e.source,
          e y i = y a / (y g) ^ k) ∧
        (∀ a : S, ContDiffOn ℂ ω (fun z => e.symm z a) e.target) := by
  obtain ⟨g, hg, n, m, P, _⟩ := Foundations.Scheme.SmoothComplexPoint.Algebraic.smooth_point_exists_submersive_presentation x
  let xg := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg
  obtain ⟨e₀, hx₀, hforward, hinverse⟩ := exists_standardSmooth_point_chart P xg
  let ιg := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g
  have hιg : Topology.IsOpenEmbedding ιg :=
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction g
  let e₁ := e₀.lift_openEmbedding hιg
  have hx₁ : x ∈ e₁.source := by
    change x ∈ ιg '' e₀.source
    refine ⟨xg, hx₀, ?_⟩
    exact Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x g hg
  have hsource : e₁.source ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g := by
    change ιg '' e₀.source ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g
    rintro y ⟨yg, _, rfl⟩
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g yg).property
  have hfractions (i : JacobianRegularity.FreeCoordinates P.map) :
      ∃ (a : S) (k : ℕ), ∀ y ∈ e₁.source, e₁ y i = y a / (y g) ^ k := by
    refine ⟨(IsLocalization.Away.sec g (P.val i.val)).1,
      (IsLocalization.Away.sec g (P.val i.val)).2, ?_⟩
    intro y hy
    change y ∈ ιg '' e₀.source at hy
    obtain ⟨yg, _, rfl⟩ := hy
    change (e₀.lift_openEmbedding hιg) (ιg yg) i = _
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, hforward]
    exact localizedPoint_eval_eq_div g yg (P.val i.val)
  have hinverse₁ (a : S) :
      ContDiffOn ℂ ω (fun z => e₁.symm z a) e₁.target := by
    change ContDiffOn ℂ ω
      (fun z => e₀.symm z (algebraMap S (Localization.Away g) a)) e₀.target
    exact hinverse (algebraMap S (Localization.Away g) a)
  let b : (JacobianRegularity.FreeCoordinates P.map → ℂ) ≃L[ℂ]
      (Fin (Fintype.card (JacobianRegularity.FreeCoordinates P.map)) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ
      (Fintype.equivFin (JacobianRegularity.FreeCoordinates P.map)).symm).toContinuousLinearEquiv
  let e := e₁.transHomeomorph b.toHomeomorph
  refine ⟨g, hg, n, m, P, e, hx₁, hsource, ?_, ?_⟩
  · intro i
    let j : JacobianRegularity.FreeCoordinates P.map := (Fintype.equivFin (JacobianRegularity.FreeCoordinates P.map)).symm i
    obtain ⟨a, k, hak⟩ := hfractions j
    refine ⟨a, k, ?_⟩
    intro y hy
    change e₁ y j = y a / (y g) ^ k
    exact hak y hy
  · intro a
    change ContDiffOn ℂ ω (fun z => e₁.symm (b.symm z) a) (b.symm ⁻¹' e₁.target)
    exact (hinverse₁ a).comp b.symm.contDiff.contDiffOn (fun _ hz => hz)

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts
