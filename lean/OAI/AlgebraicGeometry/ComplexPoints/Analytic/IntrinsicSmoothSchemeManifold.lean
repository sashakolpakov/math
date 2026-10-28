import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenTransitions
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothDimension
import OAI.AlgebraicGeometry.Betti.SmoothDimension

/-! # Intrinsic Smooth Scheme Manifold -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold

noncomputable section

/-!
# Manifolds on the native complex points of smooth integral schemes

The atlas consists of genuine regular-coordinate charts on affine opens,
lifted through their actual open immersions. Its dimension is computed from
the scheme's function field. Coverage and compatibility are consequences of
algebraic smoothness, localization, and the proved analytic implicit-function
charts, rather than additional geometric assumptions.
-/

open scoped ContDiff _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry

section StandardSmooth

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- A standard smooth algebra of relative dimension `n` has genuine regular
charts with exactly `n` complex coordinates at each of its complex points. -/
theorem exists_standardSmooth_affineRegularChart (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n ℂ A] (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ),
      e ∈ SmoothSchemeManifold.affineRegularAtlas A n ∧ x ∈ e.source := by
  classical
  let : Algebra.IsStandardSmooth ℂ A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := n)
  obtain ⟨g, hg, r, s, P, e, hx, hsource, hcoords, hinverse⟩ :=
    SmoothAffineCharts.exists_smoothAffinePoint_localChart x
  let : Nontrivial (Localization.Away g) :=
    (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg).toRingHom.domain_nontrivial
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ (Localization.Away g) :=
    Foundations.Scheme.StandardSmoothDimension.Algebraic.standardSmoothDimension_localizationAway n g
  have hdim : Nat.card (JacobianRegularity.FreeCoordinates P.map) = n := by
    simpa only [Fintype.card_eq_nat_card] using
      (Foundations.Scheme.PresentationDimension.Algebraic.card_free_variables_eq_dimension P.toPreSubmersivePresentation).trans
        (Foundations.Scheme.StandardSmoothDimension.Algebraic.standardSmooth_dimension_eq_presentation n P).symm
  have hex : ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
        (Fin (Fintype.card (JacobianRegularity.FreeCoordinates P.map)) → ℂ),
      e ∈ SmoothSchemeManifold.affineRegularAtlas A (Fintype.card (JacobianRegularity.FreeCoordinates P.map)) ∧ x ∈ e.source := by
    exact ⟨e, ⟨hinverse, ⟨g, fun _ hy => hsource hy, hcoords⟩⟩, hx⟩
  have hdim' : Fintype.card (JacobianRegularity.FreeCoordinates P.map) = n :=
    Fintype.card_eq_nat_card.trans hdim
  exact (congrArg (fun d => ∃ e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (Fin d → ℂ), e ∈ SmoothSchemeManifold.affineRegularAtlas A d ∧ x ∈ e.source) hdim').mp hex

end StandardSmooth

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The actual regular-coordinate atlas on native scheme points consists of
charts from affine open section algebras, lifted through their canonical maps. -/
def schemeRegularAtlas (n : ℕ) :
    Set (OpenPartialHomeomorph (SchemePointHomeomorphs.schemeComplexPoints X) (Fin n → ℂ)) :=
  {c | ∃ (U : X.left.Opens) (hU : IsAffineOpen U)
      (e : OpenPartialHomeomorph
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (Fin n → ℂ)),
      e ∈ SmoothSchemeManifold.affineRegularAtlas (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) n ∧
      c = SmoothSchemeManifold.affineChartOnScheme (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
        (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e}

/-- All charts in the native regular atlas have analytic transitions, since
they come from actual affine open immersions and their localization maps. -/
theorem schemeRegularAtlas_compatible {n : ℕ}
    (c d : OpenPartialHomeomorph (SchemePointHomeomorphs.schemeComplexPoints X) (Fin n → ℂ))
    (hc : c ∈ schemeRegularAtlas X n) (hd : d ∈ schemeRegularAtlas X n) :
    ContDiffOn ℂ ω (c.symm.trans d) (c.symm.trans d).source := by
  obtain ⟨U, hU, e, he, rfl⟩ := hc
  obtain ⟨V, hV, f, hf, rfl⟩ := hd
  exact AffineOpenTransitions.contDiffOn_affineOpenChartTransition
    (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
    (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)
    (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV) e f he hf

variable [IsIntegral X.left] [Smooth X.hom]

/-- Algebraic smoothness on an integral scheme supplies a regular chart at
every native complex point, of the proved common function-field dimension. -/
theorem exists_schemeRegularChart (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ c : OpenPartialHomeomorph (SchemePointHomeomorphs.schemeComplexPoints X)
        (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ),
      c ∈ schemeRegularAtlas X (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) ∧
      p ∈ c.source := by
  let n := Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom
  let : SmoothOfRelativeDimension n X.hom := Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension X.hom
  obtain ⟨U, hU, V, hV, hpV, eUV, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := X.hom) (SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  have hUtop : U = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      have hpU := eUV hpV
      exact (Subsingleton.elim (X.hom (SchemePointHomeomorphs.schemeComplexPoints.underlying p)) y) ▸ hpU
  subst U
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ
      (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) :=
    Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra_standardSmooth n X.hom V hstd
  have hp : p ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV) := by
    rw [SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
    exact hpV
  obtain ⟨x, hx⟩ := hp
  obtain ⟨e, he, hxe⟩ := exists_standardSmooth_affineRegularChart n x
  refine ⟨SmoothSchemeManifold.affineChartOnScheme (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V)
    (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV) e, ?_, ?_⟩
  · exact ⟨V, hV, e, he, rfl⟩
  · exact ⟨x, hxe, hx⟩

/-- The manifold charts on genuine scheme-valued complex points. Their
common dimension and their coverage are both theorems of algebraic smoothness. -/
instance nativeSmoothSchemeChartedSpace :
    ChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      (SchemePointHomeomorphs.schemeComplexPoints X) where
  atlas := schemeRegularAtlas X (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
  chartAt p := Classical.choose (exists_schemeRegularChart X p)
  mem_chart_source p := (Classical.choose_spec (exists_schemeRegularChart X p)).2
  chart_mem_atlas p := (Classical.choose_spec (exists_schemeRegularChart X p)).1

/-- The native complex points of every smooth integral complex scheme form a
complex analytic manifold for their proved ordinary analytic topology. -/
instance nativeSmoothSchemeComplexIsManifold (r : ℕ∞ω) :
    IsManifold (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) r
      (SchemePointHomeomorphs.schemeComplexPoints X) := by
  apply isManifold_of_contDiffOn
    (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) r _
  intro c d hc hd
  have h := (schemeRegularAtlas_compatible X c d hc hd).of_le (show r ≤ ω from le_top)
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using h

/-- Restricting scalars provides the actual underlying real smooth manifold
on which complex-valued differential forms are defined. -/
instance nativeSmoothSchemeRealIsManifold (r : ℕ∞ω) :
    IsManifold (𝓘(ℝ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) r
      (SchemePointHomeomorphs.schemeComplexPoints X) := by
  apply isManifold_of_contDiffOn
    (𝓘(ℝ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) r _
  intro c d hc hd
  have h := ((schemeRegularAtlas_compatible X c d hc hd).of_le
    (show r ≤ ω from le_top)).restrict_scalars ℝ
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using h

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold
