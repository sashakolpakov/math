import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedChosenPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOppositePoints

/-! # Prescribed Opposite Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedOppositePoints.Construction

noncomputable section

/-! Each actual opposite-block annihilator embeds in the same full
kernel prescription, retaining its original canonical pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
  (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
  (v : Fin s)
  (P : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
  (T : Over (Spec (.of k)))
  (a : T ⟶ (P.annihilatorGroup (H v).coordinates (H v).inclusion).X)

abbrev prescribedOppositePoint :=
  CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n (labels (v, true)) T
    (a ≫ (P.oppositeInclusion (H v).coordinates (H v).inclusion
      (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood
        (labels (v, false)) (labels (v, true)) (hc v) n P)).hom.hom)

theorem prescribedFullKernel_contains_opposite :
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T
      (prescribedOppositePoint j iota hsplit A ρ hρ hgood n s labels hc H v P T a).val := by
  let i := (P.oppositeInclusion (H v).coordinates (H v).inclusion
    (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood
      (labels (v, false)) (labels (v, true)) (hc v) n P)).hom.hom
  let z := CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n (labels (v, true)) T (a ≫ i)
  have hz := (CanonicalOppositePoints.Construction.canonicalOppositeKernel_realizes j iota hsplit A ρ hρ hgood
    (labels (v, false)) (labels (v, true)) (hc v) n P (H v) T (a ≫ i)).mp ⟨a, rfl⟩
  refine ⟨z, rfl, ?_⟩
  intro w
  constructor
  · have hl : labels (v, true) ≠ labels (w, false) := by
      intro he
      have hb : (true : Bool) = false := congrArg Prod.snd (labels.injective he)
      cases hb
    exact ⟨1, (CanonicalBlockProjectorPoints.Construction.prescribedChosenPoint_one A j iota hsplit ρ n (labels (w, false)) T (H w)).trans
      (CanonicalBlockProjectorPoints.Construction.canonicalOriginalBlockPoint_component_other A j iota hsplit ρ n (labels (v, true)) T
        (a ≫ i) (labels (w, false)) hl).symm⟩
  · intro U t h
    have hn := CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint_natural j iota hsplit A ρ n (labels (v, true)) t (a ≫ i)
    by_cases hvw : v = w
    · subst w
      have hp := (congrArg (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) U)
        hn.symm).trans (CanonicalBlockProjectorPoints.Construction.canonicalOriginalBlockPoint_component_self A j iota hsplit ρ n
          (labels (v, true)) U (t ≫ (a ≫ i)))
      exact (congrArg (Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
        (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h)) hp).mpr (hz U t h)
    · have hl : labels (v, true) ≠ labels (w, true) :=
        fun he => hvw (congrArg Prod.fst (labels.injective he))
      have hp := (congrArg (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (w, true)) U)
        hn.symm).trans (CanonicalBlockProjectorPoints.Construction.canonicalOriginalBlockPoint_component_other A j iota hsplit ρ n
          (labels (v, true)) U (t ≫ (a ≫ i)) (labels (w, true)) hl)
      exact (congrArg (Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
        (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (w, false)) (H w) U h)) hp).mpr
          (CanonicalBlockProjectorPoints.Construction.canonicalTorsionOrthogonal_one_right A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U _)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedOppositePoints.Construction
