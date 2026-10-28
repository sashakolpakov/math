import OAI.Analysis.HodgeTheory.Decomposition.Core
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

/-! # Mem -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem

noncomputable section

/-!
# Canonical rational weight-one Hodge structures from HodgeDecomposition

The Hodge pieces are the actual geometric Betti subspaces, pulled back by
canonical coefficient extension. Finiteness is proved from compact-manifold
cohomology. HodgeDecomposition is an explicit full input; no weight-one structure, splitting,
or identification of a chosen structure with geometry is assumed.
-/

open _root_.CategoryTheory
open scoped TensorProduct Classical
open OAI.Analysis.HodgeTheory.Decomposition.Core.Constructions

def HodgeDecompositionInput : Prop :=
  ∀
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ),
    DirectSum.IsInternal (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n) ∧
    (∃ c : X.complexCohomology n →ₛₗ[starRingEnd ℂ]
        X.complexCohomology n,
      Function.Involutive c ∧
      (∀ ω : X.componentClosedForms n,
        c (X.closedFormBettiClass n ω) =
          X.closedFormBettiClass n (Analysis.HodgeTheory.Decomposition.Core.Constructions.conjugateClosed X n ω)) ∧
      (∀ (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (x : X.complexCohomology n),
        x ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n i ↔
          c x ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i))) ∧
    (∀ p : ℤ,
      Analysis.HodgeTheory.Decomposition.Core.Constructions.deRhamFiltrationBetti X n p =
        ⨆ (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (_ : p ≤ (i.val.1 : ℤ)),
          Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n i)

def holomorphicDegree : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1 := ⟨(1, 0), rfl⟩
def antiholomorphicDegree : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1 := ⟨(0, 1), rfl⟩

theorem weight_one_degrees : (Set.univ : Set (Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1)) =
    {Mem.holomorphicDegree, Mem.antiholomorphicDegree} := by
  ext i
  rcases i with ⟨⟨a, b⟩, h⟩
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with ha | ha
  · subst a
    have hb : b = 1 := by omega
    subst b
    simp [Mem.holomorphicDegree, Mem.antiholomorphicDegree]
  · subst a
    have hb : b = 0 := by omega
    subst b
    simp [Mem.holomorphicDegree, Mem.antiholomorphicDegree]

theorem geometric_pieces_complementary (hHodgeDecomposition : HodgeDecompositionInput)
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    IsCompl (P.pureBettiSubspace 1 0) (P.pureBettiSubspace 0 1) := by
  exact DirectSum.IsInternal.isCompl (A := Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P 1)
    (by decide : holomorphicDegree ≠ antiholomorphicDegree)
    weight_one_degrees (hHodgeDecomposition P 1).1

/-- Canonical scalar extension, using the proved finiteness of actual cohomology. -/
def bettiComplexification (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    ComplexMultiplication.WeightOne.CM.Complexification (P.rationalCohomology n) ≃ₗ[ℂ] P.complexCohomology n := by
  let : FiniteDimensional ℚ (P.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite P n
  exact ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace P.toOver) n

theorem integral_complexification_conjugation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x) =
    ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
    rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul,
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
    exact (((ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V).map_smulₛₗ z
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace V.toOver) 1 c)).trans
      (congrArg (fun y : V.complexCohomology 1 => star z • y)
        (ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialH1_rational (Betti.Scheme.schemePointSpace V.toOver) c))).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem integral_conjugate_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
        (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x) ∈ V.pureBettiSubspace 0 1 ↔
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 x ∈
        V.pureBettiSubspace 1 0 := by
  constructor
  · intro hx
    have h := ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_antiholomorphic V _ hx
    rw [← integral_complexification_conjugation, ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] at h
    exact h
  · intro hx
    rw [integral_complexification_conjugation]
    exact ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_holomorphic V _ hx

def componentRestriction (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents P.carrier) :
    P.rationalCohomology 1 →ₗ[ℚ] (P.componentVariety C).rationalCohomology 1 :=
  (LinearMap.proj C).comp (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 1).toLinearMap

theorem component_complexification (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (P.rationalCohomology 1)) (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℂ ℂ) 1
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace P.toOver) 1 x) C =
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (P.componentVariety C).toOver) 1
        ((componentRestriction P C).baseChange ℂ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul z a =>
    simp only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, LinearMap.baseChange_tmul]
    change P.componentBettiEquiv (ModuleCat.of ℂ ℂ) 1
        (z • P.rationalCohomologyInclusion 1 a) C =
      z • (P.componentVariety C).rationalCohomologyInclusion 1
        (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 1 a C)
    exact (congrFun ((P.componentBettiEquiv (ModuleCat.of ℂ ℂ) 1).map_smul z
      (P.rationalCohomologyInclusion 1 a)) C).trans
      (congrArg (z • ·) (P.componentBettiEquiv_rationalInclusion 1 a C))

theorem presentation_conjugate_mem (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (P.rationalCohomology 1)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace P.toOver) 1
        (ComplexMultiplication.WeightOne.CM.coefficientConjugation (P.rationalCohomology 1) x) ∈ P.pureBettiSubspace 0 1 ↔
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace P.toOver) 1 x ∈
        P.pureBettiSubspace 1 0 := by
  rw [P.mem_pureBettiSubspace_iff, P.mem_pureBettiSubspace_iff]
  apply forall_congr'
  intro C
  rw [component_complexification, component_complexification, ComplexMultiplication.WeightOne.CM.baseChange_coefficientConjugation]
  exact integral_conjugate_mem (P.componentVariety C) _

/-- HodgeDecomposition constructs the canonical Hodge structure; its pieces are not input fields. -/
def canonicalH1 (hHodgeDecomposition : HodgeDecompositionInput) (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (P.rationalCohomology 1) where
  finiteDimensional := AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite P 1
  holomorphic := (P.pureBettiSubspace 1 0).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace P.toOver) 1)
  antiholomorphic := (P.pureBettiSubspace 0 1).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace P.toOver) 1)
  complementary := by
    let e := bettiComplexification P 1
    exact (Submodule.orderIsoMapComapOfBijective e.toLinearMap e.bijective).symm.isCompl_iff.mp
      (geometric_pieces_complementary hHodgeDecomposition P)
  conjugate_mem := presentation_conjugate_mem P

/-- A closed geometric form defines its actual complexified rational Betti class. -/
def closedFormClass (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    P.componentClosedForms 1 →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (P.rationalCohomology 1) :=
  (bettiComplexification P 1).symm.toLinearMap.comp (P.closedFormBettiClass 1)

theorem closedFormClass_holomorphic (hHodgeDecomposition : HodgeDecompositionInput)
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (ω : P.componentClosedForms 1)
    (hω : ω.val ∈ P.componentPureForms 1 0) :
    closedFormClass P ω ∈ (canonicalH1 hHodgeDecomposition P).holomorphic := by
  change (bettiComplexification P 1) ((bettiComplexification P 1).symm
    (P.closedFormBettiClass 1 ω)) ∈ P.pureBettiSubspace 1 0
  rw [LinearEquiv.apply_symm_apply]
  change P.closedFormBettiClass 1 ω ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P 1 Mem.holomorphicDegree
  rw [Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece_eq_image]
  exact ⟨ω, hω, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem
