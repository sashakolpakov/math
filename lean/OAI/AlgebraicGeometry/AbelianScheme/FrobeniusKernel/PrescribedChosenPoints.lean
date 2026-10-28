import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockProjectorPoints

/-! # Prescribed Chosen Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedChosenPoints.Construction

noncomputable section

/-! Each native chosen-block subgroup embeds in the independent full
kernel prescription. The other coefficient blocks vanish identically. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
  (T : Over (Spec (.of k))) (v : Fin s) (a : T ⟶ (H v).group.X)

theorem prescribedFullKernel_contains_chosen :
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) T a).val := by
  let z := Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) T a
  refine ⟨z, rfl, ?_⟩
  intro w
  constructor
  · by_cases hvw : v = w
    · subst w
      exact ⟨a, (CanonicalBlockProjectorPoints.Construction.canonicalOriginalBlockPoint_component_self A j iota hsplit ρ n
        (labels (v, false)) T (a ≫ (H v).inclusion.hom.hom)).symm⟩
    · have hl : labels (v, false) ≠ labels (w, false) :=
        fun h => hvw (congrArg Prod.fst (labels.injective h))
      exact ⟨1, (CanonicalBlockProjectorPoints.Construction.prescribedChosenPoint_one A j iota hsplit ρ n (labels (w, false)) T (H w)).trans
        (CanonicalBlockProjectorPoints.Construction.canonicalOriginalBlockPoint_component_other A j iota hsplit ρ n (labels (v, false)) T
          (a ≫ (H v).inclusion.hom.hom) (labels (w, false)) hl).symm⟩
  · intro U t h
    have hl : labels (v, false) ≠ labels (w, true) := by
      intro he
      have hb : (false : Bool) = true := congrArg Prod.snd (labels.injective he)
      cases hb
    have hn := CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint_natural j iota hsplit A ρ n (labels (v, false)) t
      (a ≫ (H v).inclusion.hom.hom)
    have hp := (congrArg (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (w, true)) U)
      hn.symm).trans (CanonicalBlockProjectorPoints.Construction.canonicalOriginalBlockPoint_component_other A j iota hsplit ρ n
        (labels (v, false)) U (t ≫ (a ≫ (H v).inclusion.hom.hom)) (labels (w, true)) hl)
    exact (congrArg (Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (w, false)) (H w) U h)) hp).mpr
        (CanonicalBlockProjectorPoints.Construction.canonicalTorsionOrthogonal_one_right A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U _)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedChosenPoints.Construction
