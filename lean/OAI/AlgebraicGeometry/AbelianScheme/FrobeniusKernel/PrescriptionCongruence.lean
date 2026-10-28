import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents

/-! # Prescription Congruence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionCongruence.Construction

noncomputable section

/-! The independent kernel depends only on the embedded chosen subgroup,
including its points over nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H J : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

theorem prescribedFullKernel_congr
    (he : ∀ (v : Fin s) (T : Over (Spec (.of k)))
      (a : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n).X),
      (∃ h : T ⟶ (H v).group.X, h ≫ (H v).inclusion.hom.hom = a) ↔
      (∃ h : T ⟶ (J v).group.X, h ≫ (J v).inclusion.hom.hom = a))
    (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme) :
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a ↔
      Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels J T a := by
  have forward (H J : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
      (he : ∀ (v : Fin s) (T : Over (Spec (.of k)))
        (a : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n).X),
        (∃ h : T ⟶ (H v).group.X, h ≫ (H v).inclusion.hom.hom = a) ↔
        (∃ h : T ⟶ (J v).group.X, h ≫ (J v).inclusion.hom.hom = a)) :
      Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a →
        Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels J T a := by
    rintro ⟨x, hx, hcond⟩
    refine ⟨x, hx, fun v => ⟨?_, ?_⟩⟩
    · obtain ⟨h, hh⟩ := (hcond v).1
      obtain ⟨h', hh'⟩ := (he v T _).mp ⟨h, rfl⟩
      exact ⟨h', (congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n
        (labels (v, false)) T) hh').trans hh⟩
    · intro U t h'
      obtain ⟨h, hh⟩ := (he v U _).mpr ⟨h', rfl⟩
      have hp := congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n
        (labels (v, false)) U) hh
      change Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h =
        Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (J v) U h' at hp
      exact hp ▸ (hcond v).2 U t h
  exact ⟨forward H J he, forward J H (fun v T a => (he v T a).symm)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionCongruence.Construction
