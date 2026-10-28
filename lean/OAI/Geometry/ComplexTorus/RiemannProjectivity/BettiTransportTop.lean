import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticRealizationEq
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AbelianModel

/-! # Betti Transport Top -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport

noncomputable section

/-! # RiemannProjectivity: transport of genuine singular cohomology and its coefficient map -/

open _root_.CategoryTheory
open scoped TensorProduct

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]

def topIso (e : M ≃ₜ N) : TopCat.of M ≅ TopCat.of N := TopCat.isoOfHomeo e

def iso (R : Type) [Ring R] (e : M ≃ₜ N) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) (TopCat.of N) n ≅
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) (TopCat.of M) n :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of R R) n).mapIso (topIso e).op

theorem iso_hom (R : Type) [Ring R] (e : M ≃ₜ N) (n : ℕ) :
    (iso R e n).hom = AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) (topIso e).hom n := rfl

theorem coefficient_naturality (e : M ≃ₜ N) (n : ℕ)
    (x : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) n) :
    (iso ℂ e n).hom (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of N) n x) =
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of M) n ((iso ℚ e n).hom x) := by
  rw [iso_hom, iso_hom]
  have h := AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_naturality (topIso e).hom n
  have hx := ConcreteCategory.congr_hom h x
  exact hx.symm

theorem complexification_naturality (e : M ≃ₜ N) (n : ℕ)
    (x : ℂ ⊗[ℚ] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) n) :
    (iso ℂ e n).hom (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of N) n x) =
      AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of M) n (((iso ℚ e n).hom.hom.baseChange ℂ) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
    simp only [LinearMap.baseChange_tmul, AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
    change (iso ℂ e n).hom.hom (c • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of N) n a) = _
    exact ((iso ℂ e n).hom.hom.map_smul c _).trans
      (congrArg (fun z => c • z) (coefficient_naturality e n a))

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport
