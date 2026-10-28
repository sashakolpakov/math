import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! # Affine Coordinates M -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineCoordinatesM.Constructions.AffineCoordinates

noncomputable section

/-!
# Standard affine coordinates in the native regular atlas

These compatibility lemmas concern actual polynomial-ring characters. They
do not assume analytic compatibility for an algebraic embedding.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion ChartedSpace

/-- Standard affine coordinates are a genuine chart of the regular atlas. -/
theorem polynomialChart_mem_regularAtlas (n : ℕ) :
    (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)).toOpenPartialHomeomorph ∈
      ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (MvPolynomial (Fin n) ℂ) n := by
  constructor
  · intro p
    change ContDiffOn ℂ ω (fun z => MvPolynomial.eval z p) Set.univ
    exact (AnalyticOnNhd.eval_mvPolynomial p).contDiffOn uniqueDiffOn_univ
  · refine ⟨1, ?_, ?_⟩
    · intro x _
      simp
    · intro i
      refine ⟨MvPolynomial.X i, 0, ?_⟩
      intro x _
      simp [ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph_apply]

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {n m : ℕ}

section PolynomialManifold

variable {ι : Type*} [Fintype ι]

local instance : Algebra.Smooth ℂ (MvPolynomial ι ℂ) where
  formallySmooth := inferInstance
  finitePresentation := inferInstance

local notation "PolynomialModel" =>
  (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ (MvPolynomial ι ℂ)) → ℂ)

/-- Polynomial-ring characters have their ordinary affine coordinates as
analytic functions on the native smooth manifold. -/
theorem contMDiff_polynomialPointHomeomorph (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, PolynomialModel)) (𝓘(ℂ, ι → ℂ)) r
      (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph ι) := by
  apply contMDiff_pi_space.mpr
  intro i
  exact ComplexPoints.Analytic.SmoothAffineMaps.contMDiff_smoothDomain_eval (MvPolynomial.X i) r

/-- Conversely, polynomial evaluation is analytic in the native regular
atlas; its chart expressions are the atlas's actual rational functions. -/
theorem contMDiff_polynomialPointHomeomorph_symm (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, ι → ℂ)) (𝓘(ℂ, PolynomialModel)) r
      (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph ι).symm := by
  apply contMDiff_iff.mpr
  refine ⟨(ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph ι).symm.continuous, ?_⟩
  intro x y
  have he : chartAt PolynomialModel y ∈
      ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (MvPolynomial ι ℂ)
        (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ (MvPolynomial ι ℂ)) :=
    chart_mem_atlas PolynomialModel y
  obtain ⟨g, hg, hcoords⟩ := he.2
  have hc : ContDiffOn ℂ ω
      (fun z => chartAt PolynomialModel y ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph ι).symm z))
      {z | (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph ι).symm z ∈
        (chartAt PolynomialModel y).source} := by
    apply contDiffOn_pi.mpr
    intro i
    obtain ⟨a, k, ha⟩ := hcoords i
    have hp (p : MvPolynomial ι ℂ) : ContDiff ℂ ω (fun z => MvPolynomial.eval z p) :=
      contDiffOn_univ.mp ((AnalyticOnNhd.eval_mvPolynomial p).contDiffOn uniqueDiffOn_univ)
    apply ((hp a).contDiffOn.div ((hp g).contDiffOn.pow k) (fun z hz =>
      pow_ne_zero k (hg _ hz))).congr
    intro z hz
    exact ha _ hz
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_target,
    OpenPartialHomeomorph.refl_symm, Set.univ_inter, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.mem_univ, Set.ofPred_true]
    using hc.of_le (show r ≤ ω from le_top)

end PolynomialManifold

/-- An algebraic map to affine space has analytic standard coordinates in
every regular source chart. -/
theorem contDiffOn_polynomial_coordinates
    (h : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m) :
    ContDiffOn ℂ ω
      (fun z => ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n) ((e.symm z).comp h)) e.target := by
  apply contDiffOn_pi.mpr
  intro i
  exact he.1 (h (MvPolynomial.X i))

/-- Surjectivity of the coordinate-ring map proves injectivity of the actual
standard-coordinate derivative of an affine closed immersion. -/
theorem fderiv_polynomial_coordinates_injective
    (h : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (hh : Function.Surjective h)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    Function.Injective (fderiv ℂ
      (fun z => ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n) ((e.symm z).comp h)) (e x)) := by
  exact ComplexPoints.Analytic.SmoothClosedImmersion.fderiv_affineChartComap_injective_of_surjective h hh e
    (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)).toOpenPartialHomeomorph he
    (polynomialChart_mem_regularAtlas n) x hx (Set.mem_univ _)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AffineCoordinatesM.Constructions.AffineCoordinates
