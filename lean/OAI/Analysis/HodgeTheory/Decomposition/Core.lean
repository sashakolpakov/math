import OAI.AlgebraicGeometry.Betti.ProjectivePresentationComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import Mathlib.Algebra.DirectSum.Module

/-! # Core -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Core.Constructions

noncomputable section

abbrev Bidegree (n : ℕ) :=
  { pq : ℕ × ℕ // pq.1 + pq.2 = n }

def swapBidegree {n : ℕ} (i : Bidegree n) : Bidegree n :=
  ⟨(i.val.2, i.val.1),
    (Nat.add_comm i.val.2 i.val.1).trans i.property⟩

/-- The existing pure Betti subspace, transported to degree `n`. -/
def hodgePiece (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (i : Bidegree n) :
    Submodule ℂ (X.complexCohomology n) :=
  i.property ▸ X.pureBettiSubspace i.val.1 i.val.2

def pureFormsAt (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (i : Bidegree n) :
    Submodule ℂ (X.componentForms n) :=
  i.property ▸ X.componentPureForms i.val.1 i.val.2

/-- The filtration on smooth forms, defined independently of cohomology. -/
def filteredForms (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (p : ℤ) : Submodule ℂ (X.componentForms n) :=
  ⨆ (i : Bidegree n) (_ : p ≤ (i.val.1 : ℤ)),
    pureFormsAt X n i

/-- Closed filtered forms mapped to Betti cohomology by canonical comparison. -/
def deRhamFiltrationBetti (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (p : ℤ) : Submodule ℂ (X.complexCohomology n) :=
  ((filteredForms X n p).comap
    (X.componentClosedForms n).subtype).map
      (X.closedFormBettiClass n)

/-- Pointwise complex conjugation of closed forms on each component. -/
def conjugateClosed (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (form : X.componentClosedForms n) :
    X.componentClosedForms n :=
  (X.componentClosedFormsEquiv n).symm
    (fun C => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm
      (X.componentClosedFormsEquiv n form C))

section ManifoldConjugation

open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Conjugation commutes with the incoming derivative, including degree zero. -/
theorem conjugate_incoming (n : ℕ)
    (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (n - 1)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative E M n form) =
      DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative E M n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm form) := by
  cases n with
  | zero => simp
  | succ n => exact (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm form).symm

/-- Conjugation therefore preserves exact forms in every degree. -/
theorem conjugate_exact (n : ℕ) (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (hform : form ∈ DifferentialForms.Manifold.ManifoldDeRham.manifoldExactForms E M n) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm form ∈ DifferentialForms.Manifold.ManifoldDeRham.manifoldExactForms E M n := by
  obtain ⟨η, rfl⟩ := hform
  exact ⟨AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm η, (conjugate_incoming n η).symm⟩

end ManifoldConjugation

/-- Conjugation of a closed family is an involution. -/
theorem conjugateClosed_involutive (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    Function.Involutive (conjugateClosed X n) := by
  intro form
  apply (X.componentClosedFormsEquiv n).injective
  funext C
  simp only [conjugateClosed, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm_involutive _

/-- Conjugation on closed families is conjugate-linear. -/
def conjugateClosedMap (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    X.componentClosedForms n →ₛₗ[starRingEnd ℂ] X.componentClosedForms n where
  toFun := conjugateClosed X n
  map_add' form η := by
    apply (X.componentClosedFormsEquiv n).injective
    funext C
    simp only [conjugateClosed, map_add, LinearEquiv.apply_symm_apply, Pi.add_apply]
    exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedFormMap.map_add _ _
  map_smul' z form := by
    apply (X.componentClosedFormsEquiv n).injective
    funext C
    simp only [conjugateClosed, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply]
    exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedFormMap.map_smulₛₗ z _

/-- The involution preserves the genuine exact-family subspace. -/
theorem conjugateClosed_exact (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (form : X.componentClosedForms n) (hform : form ∈ X.componentExactClosedForms n) :
    conjugateClosed X n form ∈ X.componentExactClosedForms n := by
  change (conjugateClosed X n form).val ∈ X.componentExactForms n
  rw [X.mem_componentExactForms_iff]
  have h := (X.mem_componentExactForms_iff n form.val).mp hform
  intro C
  have hc := conjugate_exact n
    (X.componentClosedFormsEquiv n form C).val (h C)
  change (X.componentClosedFormsEquiv n (conjugateClosed X n form) C).val ∈ _
  rw [conjugateClosed, LinearEquiv.apply_symm_apply]
  exact hc

/-- Descending pointwise conjugation through the actual closed/exact quotient. -/
def conjugateQuotient (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    (X.componentClosedForms n ⧸ X.componentExactClosedForms n)
      →ₛₗ[starRingEnd ℂ]
    (X.componentClosedForms n ⧸ X.componentExactClosedForms n) :=
  (X.componentExactClosedForms n).mapQ (X.componentExactClosedForms n)
    (conjugateClosedMap X n) (conjugateClosed_exact X n)

/-- The integration-normalized comparison from the literal form quotient. -/
def quotientBettiEquiv (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    (X.componentClosedForms n ⧸ X.componentExactClosedForms n) ≃ₗ[ℂ]
      X.complexCohomology n :=
  (X.componentDeRhamQuotientEquiv n).trans (X.deRhamBettiEquiv n)

@[simp]
theorem quotientBettiEquiv_mk (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (form : X.componentClosedForms n) :
    quotientBettiEquiv X n ((X.componentExactClosedForms n).mkQ form) =
      X.closedFormBettiClass n form := rfl

/-- The actual Betti involution obtained by conjugating closed representatives. -/
def bettiConjugation (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    X.complexCohomology n →ₛₗ[starRingEnd ℂ] X.complexCohomology n :=
  (quotientBettiEquiv X n).toLinearMap.comp
    ((conjugateQuotient X n).comp (quotientBettiEquiv X n).symm.toLinearMap)

@[simp]
theorem bettiConjugation_class (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (form : X.componentClosedForms n) :
    bettiConjugation X n (X.closedFormBettiClass n form) =
      X.closedFormBettiClass n (conjugateClosed X n form) := by
  rw [← quotientBettiEquiv_mk X n form]
  simp only [bettiConjugation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact quotientBettiEquiv_mk X n (conjugateClosed X n form)

theorem closedFormBettiClass_surjective (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    Function.Surjective (X.closedFormBettiClass n) :=
  (X.deRhamBettiEquiv n).surjective.comp (X.componentDeRhamClass_surjective n)

theorem bettiConjugation_involutive (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    Function.Involutive (bettiConjugation X n) := by
  intro x
  obtain ⟨form, rfl⟩ := closedFormBettiClass_surjective X n x
  rw [bettiConjugation_class, bettiConjugation_class, conjugateClosed_involutive]

/-- Degree transport does not change the geometric eigencharacter criterion. -/
theorem mem_pureFormsAt_iff_action (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i : Bidegree n) (form : X.componentForms n) :
    form ∈ pureFormsAt X n i ↔
      ∀ C (z : ℂˣ), DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z (form C) =
        (((z : ℂ) ^ i.val.1)⁻¹ * ((star (z : ℂ)) ^ i.val.2)⁻¹) • form C := by
  rcases i with ⟨⟨p, q⟩, h⟩
  subst n
  change form ∈ X.componentPureForms p q ↔ _
  rw [X.mem_componentPureForms_iff]
  apply forall_congr'
  intro C
  rw [DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree,
    DifferentialForms.Manifold.CovectorAction.hasTangentBidegree_iff_section_action]
  apply forall_congr'
  intro z
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg Subtype.val h

theorem conjugateClosed_component (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (form : X.componentClosedForms n) (C : irreducibleComponents X.carrier) :
    (conjugateClosed X n form).val C = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (form.val C) := by
  change (X.componentClosedFormsEquiv n (conjugateClosed X n form) C).val = _
  rw [conjugateClosed, LinearEquiv.apply_symm_apply]
  rfl

section TypeConjugation

open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem conjugate_complexAction (n : ℕ) (z : ℂˣ) (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z form) =
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm form) := by
  apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  rfl

end TypeConjugation

/-- Complex conjugation swaps the pure types of actual closed forms. -/
theorem conjugateClosed_pure (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i : Bidegree n) (form : X.componentClosedForms n)
    (hform : form.val ∈ pureFormsAt X n i) :
    (conjugateClosed X n form).val ∈ pureFormsAt X n (swapBidegree i) := by
  rw [mem_pureFormsAt_iff_action] at hform ⊢
  intro C z
  rw [conjugateClosed_component, ← conjugate_complexAction, hform C z]
  have h := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothFormMap.map_smulₛₗ
    ((((z : ℂ) ^ i.val.1)⁻¹ * ((star (z : ℂ)) ^ i.val.2)⁻¹)) (form.val C)
  simpa only [swapBidegree, starRingEnd_apply, star_mul, star_inv₀,
    star_pow, star_star, mul_comm, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothFormMap,
    LinearMap.coe_mk, AddHom.coe_mk] using h

/-- The prescribed Hodge subspace is the image of the actual pure closed forms. -/
theorem hodgePiece_eq_image (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i : Bidegree n) :
    hodgePiece X n i =
      ((pureFormsAt X n i).comap (X.componentClosedForms n).subtype).map
        (X.closedFormBettiClass n) := by
  rcases i with ⟨⟨p, q⟩, h⟩
  subst n
  change X.pureBettiSubspace p q =
    ((X.componentPureForms p q).comap (X.componentClosedForms (p + q)).subtype).map _
  rw [X.pureBettiSubspace_eq_deRhamImage]
  simp only [AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureDeRhamSubspace,
    AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureClosedForms, Submodule.map_comp,
    AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.closedFormBettiClass]

/-- Pointwise conjugation induces the required exchange on cohomology. -/
theorem bettiConjugation_mem_swap (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i : Bidegree n) (x : X.complexCohomology n)
    (hx : x ∈ hodgePiece X n i) :
    bettiConjugation X n x ∈ hodgePiece X n (swapBidegree i) := by
  rw [hodgePiece_eq_image] at hx ⊢
  obtain ⟨form, hform, rfl⟩ := hx
  exact ⟨conjugateClosed X n form, conjugateClosed_pure X n i form hform,
    (bettiConjugation_class X n form).symm⟩

theorem swapBidegree_involutive (n : ℕ) :
    Function.Involutive (@swapBidegree n) := by
  intro i
  apply Subtype.ext
  rfl

theorem bettiConjugation_mem_iff (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i : Bidegree n) (x : X.complexCohomology n) :
    x ∈ hodgePiece X n i ↔
      bettiConjugation X n x ∈ hodgePiece X n (swapBidegree i) := by
  constructor
  · exact bettiConjugation_mem_swap X n i x
  · intro hx
    have h := bettiConjugation_mem_swap X n (swapBidegree i) (bettiConjugation X n x) hx
    rwa [bettiConjugation_involutive, swapBidegree_involutive] at h

/-- The complete conjugation clause of HodgeDecomposition, with no decomposition hypothesis. -/
theorem conjugation_clause (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    ∃ c : X.complexCohomology n →ₛₗ[starRingEnd ℂ] X.complexCohomology n,
      Function.Involutive c ∧
      (∀ form : X.componentClosedForms n,
        c (X.closedFormBettiClass n form) =
          X.closedFormBettiClass n (conjugateClosed X n form)) ∧
      (∀ (i : Bidegree n) (x : X.complexCohomology n),
        x ∈ hodgePiece X n i ↔ c x ∈ hodgePiece X n (swapBidegree i)) :=
  ⟨bettiConjugation X n, bettiConjugation_involutive X n,
    bettiConjugation_class X n, bettiConjugation_mem_iff X n⟩

/-- The sum of the required Hodge pieces is contained in the de Rham filtration. -/
theorem hodge_sum_le_filtration (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (p : ℤ) :
    (⨆ (i : Bidegree n) (_ : p ≤ (i.val.1 : ℤ)), hodgePiece X n i) ≤
      deRhamFiltrationBetti X n p := by
  refine iSup_le fun i => iSup_le fun hip => ?_
  rw [hodgePiece_eq_image]
  apply Submodule.map_mono
  apply Submodule.comap_mono
  exact le_iSup_of_le i (le_iSup_of_le hip le_rfl)

/-- This is a decreasing filtration on Betti cohomology. -/
theorem deRhamFiltrationBetti_antitone (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    Antitone (deRhamFiltrationBetti X n) := by
  intro p q hpq
  apply Submodule.map_mono
  apply Submodule.comap_mono
  refine iSup_le fun i => iSup_le fun hqi => ?_
  exact le_iSup_of_le i (le_iSup_of_le (hpq.trans hqi) le_rfl)

/-- The filtration is zero above the total cohomological degree. -/
theorem filteredForms_eq_bot_of_degree_lt (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (p : ℤ) (hp : (n : ℤ) < p) : filteredForms X n p = ⊥ := by
  apply le_antisymm _ bot_le
  refine iSup_le fun i => iSup_le fun hi => ?_
  have hdegree := i.property
  have hbound : i.val.1 ≤ n := by omega
  have hn : (i.val.1 : ℤ) ≤ n := Int.ofNat_le.mpr hbound
  exact False.elim ((not_le_of_gt hp) (hi.trans hn))

theorem filtration_eq_bot_of_degree_lt (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (n : ℕ) (p : ℤ) (hp : (n : ℤ) < p) :
    deRhamFiltrationBetti X n p = ⊥ := by
  unfold deRhamFiltrationBetti
  rw [filteredForms_eq_bot_of_degree_lt X n p hp,
    Submodule.comap_bot, Submodule.ker_subtype, Submodule.map_bot]

/-- There is exactly one Hodge bidegree in total degree zero. -/
def zeroBidegree : Bidegree 0 := ⟨(0, 0), rfl⟩

theorem bidegree_zero_eq (i : Bidegree 0) : i = zeroBidegree := by
  apply Subtype.ext
  have h := i.property
  apply Prod.ext <;> dsimp [zeroBidegree] <;> omega

/-- Every actual degree-zero form has type (0,0). -/
theorem pureFormsAt_zero_eq_top (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (i : Bidegree 0) : pureFormsAt X 0 i = ⊤ := by
  rw [bidegree_zero_eq i]
  apply top_unique
  intro form _
  change form ∈ X.componentPureForms 0 0
  rw [X.mem_componentPureForms_iff]
  intro C e he y hy
  exact DifferentialForms.Manifold.Bidegree.hasBidegree_zero _ _

theorem hodgePiece_zero_eq_top (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (i : Bidegree 0) : hodgePiece X 0 i = ⊤ := by
  rw [hodgePiece_eq_image, pureFormsAt_zero_eq_top, Submodule.comap_top,
    Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (closedFormBettiClass_surjective X 0)

/-- The Hodge decomposition holds in degree zero. -/
theorem hodge_decomposition_zero (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    DirectSum.IsInternal (hodgePiece X 0) := by
  let : Subsingleton (Bidegree 0) :=
    ⟨fun i j => (bidegree_zero_eq i).trans (bidegree_zero_eq j).symm⟩
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_subsingleton _)
  apply top_unique
  exact le_iSup_of_le zeroBidegree (hodgePiece_zero_eq_top X zeroBidegree).ge

/-- The full filtration equality holds in degree zero. -/
theorem filtration_zero (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℤ) :
    deRhamFiltrationBetti X 0 p =
      ⨆ (i : Bidegree 0) (_ : p ≤ (i.val.1 : ℤ)), hodgePiece X 0 i := by
  by_cases hp : p ≤ 0
  · apply le_antisymm _ (hodge_sum_le_filtration X 0 p)
    exact le_top.trans (le_iSup_of_le zeroBidegree
      (le_iSup_of_le hp (hodgePiece_zero_eq_top X zeroBidegree).ge))
  · have hp' : (0 : ℤ) < p := lt_of_not_ge hp
    rw [filtration_eq_bot_of_degree_lt X 0 p hp']
    apply le_antisymm bot_le
    refine iSup_le fun i => iSup_le fun hi => ?_
    rw [bidegree_zero_eq i] at hi
    exact False.elim (hp hi)

end

end OAI.Analysis.HodgeTheory.Decomposition.Core.Constructions
