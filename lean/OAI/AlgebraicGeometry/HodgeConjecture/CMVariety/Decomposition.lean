import OAI.Analysis.HodgeTheory.Decomposition.Definitions
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntegralPieces
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Pairing

/-! # Decomposition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Decomposition.CM.Abelian

noncomputable section

/-! The exact HodgeDecomposition input and the resulting diagonal/off-diagonal spanning decomposition. -/

open OAI.Analysis.HodgeTheory.Decomposition.Definitions

def HodgeDecompositionInput : Prop :=
  ∀ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ),
    DirectSum.IsInternal (Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X n) ∧
    (∃ c : X.complexCohomology n →ₛₗ[starRingEnd ℂ]
        X.complexCohomology n,
      Function.Involutive c ∧
      (∀ ω : X.componentClosedForms n,
        c (X.closedFormBettiClass n ω) =
          X.closedFormBettiClass n (Analysis.HodgeTheory.Decomposition.Definitions.conjugateClosed X n ω)) ∧
      (∀ (i : Analysis.HodgeTheory.Decomposition.Definitions.Bidegree n) (x : X.complexCohomology n),
        x ∈ Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X n i ↔
          c x ∈ Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X n (Analysis.HodgeTheory.Decomposition.Definitions.swapBidegree i))) ∧
    (∀ p : ℤ,
      Analysis.HodgeTheory.Decomposition.Definitions.deRhamFiltrationBetti X n p =
        ⨆ (i : Analysis.HodgeTheory.Decomposition.Definitions.Bidegree n) (_ : p ≤ (i.val.1 : ℤ)),
          Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X n i)

def diagonalBidegree (p : ℕ) : Analysis.HodgeTheory.Decomposition.Definitions.Bidegree (p + p) := ⟨(p, p), rfl⟩

def offDiagonalBettiSubspace (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Submodule ℂ (X.complexCohomology (p + p)) :=
  ⨆ i : Analysis.HodgeTheory.Decomposition.Definitions.Bidegree (p + p), ⨆ (_ : i ≠ diagonalBidegree p), Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X.presentation (p + p) i

theorem bidegree_ne_diagonal_iff (p : ℕ) (i : Analysis.HodgeTheory.Decomposition.Definitions.Bidegree (p + p)) :
    i ≠ diagonalBidegree p ↔ i.val.1 ≠ i.val.2 := by
  constructor
  · intro hi he
    apply hi
    apply Subtype.ext
    apply Prod.ext
    · have h := i.property
      change i.val.1 = p
      omega
    · have h := i.property
      change i.val.2 = p
      omega
  · intro hi he
    apply hi
    rw [he]
    rfl

theorem hodgePiece_diagonal (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X.presentation (p + p) (diagonalBidegree p) = X.pureBettiSubspace p p :=
  IntegralPieces.CM.Abelian.integralPresentation_pureBettiSubspace X p p

theorem diagonal_sup_offDiagonal (hHodgeDecomposition : HodgeDecompositionInput)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    X.pureBettiSubspace p p ⊔ offDiagonalBettiSubspace X p = ⊤ := by
  have htotal := (hHodgeDecomposition X.presentation (p + p)).1.submodule_iSup_eq_top
  have h := Pairing.CM.Abelian.distinguished_sup_others_eq_top (Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X.presentation (p + p))
    htotal (diagonalBidegree p)
  rw [hodgePiece_diagonal] at h
  exact h

theorem hodgePiece_mem_iff_native (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (i : Analysis.HodgeTheory.Decomposition.Definitions.Bidegree n) (a : X.complexCohomology n) :
    a ∈ Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X.presentation n i ↔
      cast (congrArg (fun k => (X.complexCohomology k : Type)) i.property.symm) a ∈
        X.pureBettiSubspace i.val.1 i.val.2 := by
  obtain ⟨⟨p, q⟩, h⟩ := i
  cases h
  change a ∈ X.presentation.pureBettiSubspace p q ↔ a ∈ X.pureBettiSubspace p q
  rw [IntegralPieces.CM.Abelian.integralPresentation_pureBettiSubspace]

theorem linearMap_eq_zero_on_offDiagonal {V : Type*} [AddCommGroup V] [Module ℂ V]
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (f : X.complexCohomology (p + p) →ₗ[ℂ] V)
    (hf : ∀ i : Analysis.HodgeTheory.Decomposition.Definitions.Bidegree (p + p), i ≠ diagonalBidegree p →
      ∀ a ∈ Analysis.HodgeTheory.Decomposition.Definitions.hodgePiece X.presentation (p + p) i, f a = 0)
    (a : X.complexCohomology (p + p)) (ha : a ∈ offDiagonalBettiSubspace X p) : f a = 0 := by
  have hs : offDiagonalBettiSubspace X p ≤ LinearMap.ker f := by
    apply iSup_le
    intro i
    apply iSup_le
    intro hi v hv
    exact hf i hi v hv
  exact hs ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Decomposition.CM.Abelian
