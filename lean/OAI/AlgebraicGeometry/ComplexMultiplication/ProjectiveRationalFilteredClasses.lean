import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.FiltrationIntersection
import OAI.Analysis.HodgeTheory.Decomposition.Constructions
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveBettiConjugation

/-! # Projective Rational Filtered Classes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveRationalFilteredClasses

noncomputable section

/-! # Rational middle filtered classes have genuine Hodge type (p,p) -/

open _root_.CategoryTheory

open OAI.Analysis.HodgeTheory.Decomposition.Constructions

set_option backward.isDefEq.respectTransparency false in
/-- Actual conjugation of closed forms fixes every rational class in positive degree. -/
theorem projectiveBettiConjugation_rational_positive (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (a : P.rationalCohomology (n + 1)) :
    Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation P (n + 1) (P.rationalCohomologyInclusion (n + 1) a) =
      P.rationalCohomologyInclusion (n + 1) a := by
  obtain ⟨form, hf⟩ := Analysis.HodgeTheory.Decomposition.Core.Constructions.closedFormBettiClass_surjective P (n + 1)
    (P.rationalCohomologyInclusion (n + 1) a)
  rw [← hf, Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_class]
  apply (P.componentBettiEquiv (ModuleCat.of ℂ ℂ) (n + 1)).injective
  funext C
  rw [P.componentBettiEquiv_closedFormBettiClass,
    P.componentBettiEquiv_closedFormBettiClass]
  have he := congrArg (fun z => P.componentBettiEquiv (ModuleCat.of ℂ ℂ) (n + 1) z C) hf
  rw [P.componentBettiEquiv_closedFormBettiClass] at he
  have he' := P.componentBettiEquiv_rationalInclusion (n + 1) a C
  change P.componentBettiEquiv (ModuleCat.of ℂ ℂ) (n + 1)
    (P.rationalCohomologyInclusion (n + 1) a) C = _ at he'
  have he := he.trans he'
  have hc : P.componentClosedFormsEquiv (n + 1) (Analysis.HodgeTheory.Decomposition.Core.Constructions.conjugateClosed P (n + 1) form) C =
      HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm (P.componentClosedFormsEquiv (n + 1) form C) := by
    simp only [Analysis.HodgeTheory.Decomposition.Core.Constructions.conjugateClosed, LinearEquiv.apply_symm_apply]
  rw [hc]
  exact (HodgeComparison.PositiveBettiConjugation.CM.Construction.rational_formClass_conjugate (P.componentVariety C) n _ _ he).trans he.symm

/-- The middle-intersection lemma with the native cohomological degree spelling. -/
theorem bidegree_filtration_intersection_add {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) (S : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree (p + p) → Submodule ℂ V) (h : DirectSum.IsInternal S)
    (c : V →ₛₗ[starRingEnd ℂ] V) (hc : Function.Involutive c)
    (hS : ∀ i x, x ∈ S i → c x ∈ S (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i))
    (x : V) (hx : x ∈ ⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.1), S i)
    (hcx : c x ∈ ⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.1), S i) :
    x ∈ S ⟨(p, p), by omega⟩ := by
  classical
  have hmap : (⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.1), S i) ≤
      (⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.2), S i).comap c := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro a ha
    change c a ∈ ⨆ j, ⨆ (_ : (p : ℤ) ≤ j.val.2), S j
    apply Submodule.mem_iSup_of_mem (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i)
    apply Submodule.mem_iSup_of_mem hi
    exact hS i a ha
  have hx' : x ∈ ⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.2), S i := by
    have hh := hmap hcx
    change c (c x) ∈ ⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.2), S i at hh
    rwa [hc x] at hh
  apply SumFiltrationIntersection.internalSum_selected_intersection S h
    (fun i => (p : ℤ) ≤ i.val.1) (fun i => (p : ℤ) ≤ i.val.2)
      ⟨(p, p), by omega⟩ ?_ ⟨hx, hx'⟩
  intro i h₁ h₂
  apply Subtype.ext
  apply Prod.ext
  · have hi := i.property
    dsimp at hi h₁ h₂ ⊢
    omega
  · have hi := i.property
    dsimp at hi h₁ h₂ ⊢
    omega

set_option backward.isDefEq.respectTransparency false in
/-- In degree `2p`, membership in the actual smooth Betti filtration suffices for rational purity. -/
theorem projectiveRationalFiltered_mem_pure (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (a : P.rationalCohomology (p + p))
    (ha : P.rationalCohomologyInclusion (p + p) a ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.deRhamFiltrationBetti P (p + p) p) :
    P.rationalCohomologyInclusion (p + p) a ∈ P.pureBettiSubspace p p := by
  have hs := (Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration P (p + p)).2.2 (p : ℤ)
  rw [hs] at ha
  cases p with
  | zero =>
    have hle : (⨆ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree (0 + 0), ⨆ (_ : (0 : ℤ) ≤ i.val.1),
        Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P (0 + 0) i) ≤ P.pureBettiSubspace 0 0 := by
      refine iSup_le fun i => iSup_le fun _ => ?_
      have hi : i = ⟨(0, 0), rfl⟩ := by
        apply Subtype.ext
        apply Prod.ext <;> have h := i.property <;> dsimp at h ⊢ <;> omega
      subst i
      exact le_rfl
    exact hle ha
  | succ p =>
    have hc' : Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation P ((p + 1) + (p + 1))
        (P.rationalCohomologyInclusion ((p + 1) + (p + 1)) a) =
          P.rationalCohomologyInclusion ((p + 1) + (p + 1)) a := by
      generalize hn : (p + 1) + (p + 1) = n at a ⊢
      cases n with
      | zero => omega
      | succ n => exact projectiveBettiConjugation_rational_positive P n a
    have hswap := Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_mem_iff P ((p + 1) + (p + 1))
    have hm := bidegree_filtration_intersection_add (p + 1)
      (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece P ((p + 1) + (p + 1)))
      (Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration P ((p + 1) + (p + 1))).1
      (Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation P ((p + 1) + (p + 1)))
      (Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_involutive P ((p + 1) + (p + 1)))
      (fun i x hx => (hswap i x).mp hx) _ ha (hc'.symm ▸ ha)
    simpa only [Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece] using hm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveRationalFilteredClasses
