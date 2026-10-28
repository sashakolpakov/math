import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointProjectors
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointAlternation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedEmbeddingLabels
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitPairingFormula

/-! # Reference Point Split Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointSplitFormula.Construction

noncomputable section

/-! Recover the original canonical pairing from its conjugate block
restrictions. Completeness, adjointness and alternation are proved from
the actual source datum rather than supplied as pairing compatibilities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (n s : ℕ)
  (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hc : ∀ i, labels (i, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (i, false))
  (T : Over (Spec (.of k)))

include hρ hc in
theorem originalPointPairing_split_formula
    (x y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    let b := ReferencePointBicharacter.Construction.originalPointBicharacter A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
    b x y = ∏ i : Fin s,
      b (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (i, false)) T x)
        (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (i, true)) T y) /
      b (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (i, false)) T y)
        (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (i, true)) T x) := by
  let e := PairedEmbeddingLabels.Construction.pairedEmbeddingLabels s labels
  let p (i : Fin s ⊕ Fin s) := ReferencePointProjectors.Construction.originalPointProjector j iota hsplit A ρ n T (e i)
  have ho (i a : Fin s ⊕ Fin s) (hia : i ≠ a)
      (z : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) : p i (p a z) = 1 :=
    ReferencePointProjectors.Construction.originalPointProjectors_orthogonal j iota hsplit A ρ n T (e i) (e a)
      (fun h => hia (e.injective h)) z
  have hs (z : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) : (∏ i, p i z) = z :=
    (e.prod_comp (fun τ => ReferencePointProjectors.Construction.originalPointProjector j iota hsplit A ρ n T τ z)).trans
      (ReferencePointProjectors.Construction.originalPointProjectors_complete j iota hsplit A ρ n T z)
  let b := ReferencePointBicharacter.Construction.originalPointBicharacter A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
  have ha (i : Fin s ⊕ Fin s) (z w : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
      b (p i z) w = b z (p (Sum.swap i) w) := by
    have h := ReferencePointProjectors.Construction.originalPointProjectors_adjoint j iota hsplit A ρ n T hρ (e i) z w
    exact h.trans (congrArg (fun τ => b z (ReferencePointProjectors.Construction.originalPointProjector j iota hsplit A ρ n T τ w))
      (PairedEmbeddingLabels.Construction.pairedEmbeddingLabels_conjugate s labels hc i).symm)
  exact IsogenyQuotient.SplitPairingFormula.Construction.pairing_split_projector_formula b p ho hs ha
    (ReferencePointAlternation.Construction.originalPointBicharacter_skew A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T) x y

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointSplitFormula.Construction
