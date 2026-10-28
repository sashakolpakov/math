import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedOppositePoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockOrthogonality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenAnnihilatorAtLevel

/-! # Prescribed Maximality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedMaximality.Construction

noncomputable section

/-! Orthogonality to the full independent kernel prescription forces
membership in every chosen block and every opposite annihilator. -/

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
  (T : Over (Spec (.of k))) (y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))

def PrescribedKernelOrthogonal : Prop :=
  ∀ (U : Over (Spec (.of k))) (t : U ⟶ T)
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op U)),
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H U x.val →
      Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U x
        ((A.abelian.torsionFunctor (q ^ n)).map t.op y)

include hρ hc in
theorem prescribedOrthogonal_opposite_component
    (h : PrescribedKernelOrthogonal j iota hsplit A ρ n s labels H T y) (v : Fin s)
    (U : Over (Spec (.of k))) (t : U ⟶ T) (a : U ⟶ (H v).group.X) :
    Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U a)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) U
        ((A.abelian.torsionFunctor (q ^ n)).map t.op y)) := by
  have hz := h U t _ (PrescribedChosenPoints.Construction.prescribedFullKernel_contains_chosen j iota hsplit A ρ n s labels H U v a)
  have hp := (CanonicalBlockOrthogonality.Construction.canonicalBlockOrthogonal_project_target A j iota hsplit ρ hρ n
    (labels (v, false)) U (a ≫ (H v).inclusion.hom.hom)
    ((A.abelian.torsionFunctor (q ^ n)).map t.op y)).mp hz
  exact (congrArg (fun τ => Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
    (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U a)
    (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ U
      ((A.abelian.torsionFunctor (q ^ n)).map t.op y))) (hc v).symm).mp hp

include hρ hgood hc in
theorem prescribedOrthogonal_chosen_component
    (h : PrescribedKernelOrthogonal j iota hsplit A ρ n s labels H T y) (v : Fin s)
    (P : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n)) :
    ∃ a : T ⟶ (H v).group.X,
      Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) T a =
        Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, false)) T y := by
  let x := IntrinsicBlockComponents.Construction.nativeBlockComponent j iota hsplit A ρ n (labels (v, false)) T y
  have hx : ∃ a : T ⟶ (H v).group.X, a ≫ (H v).inclusion.hom.hom = x := by
    apply (ChosenAnnihilatorAtLevel.Construction.canonicalChosenAnnihilator_realizes_atLevel j iota hsplit A ρ hρ hgood
      (labels (v, false)) (labels (v, true)) (hc v) n P (H v) T x).mp
    intro U t a
    let i := (P.oppositeInclusion (H v).coordinates (H v).inclusion
      (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood
        (labels (v, false)) (labels (v, true)) (hc v) n P)).hom.hom
    let z := PrescribedOppositePoints.Construction.prescribedOppositePoint j iota hsplit A ρ hρ hgood n s labels hc H v P U a
    have hz := h U t z
      (PrescribedOppositePoints.Construction.prescribedFullKernel_contains_opposite j iota hsplit A ρ hρ hgood n s labels hc H v P U a)
    have hp := (CanonicalBlockOrthogonality.Construction.canonicalBlockOrthogonal_project_target A j iota hsplit ρ hρ n
      (labels (v, true)) U (a ≫ i) ((A.abelian.torsionFunctor (q ^ n)).map t.op y)).mp hz
    have hlabel : PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, true) = labels (v, false) := by
      rw [hc, ← mul_assoc, PELModuli.CMPoints.Models.rationalConjugation_mul_self, one_mul]
    have hr := (congrArg (fun τ => Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U z (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ U
        ((A.abelian.torsionFunctor (q ^ n)).map t.op y))) hlabel).mp hp
    have hs := CanonicalBlockOrthogonality.Construction.canonicalTorsionOrthogonal_symm A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U z _ hr
    have hv := (congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n (labels (v, false)) U)
      (IntrinsicBlockComponents.Construction.nativeBlockComponent_natural j iota hsplit A ρ n (labels (v, false)) t y)).trans
        (IntrinsicBlockComponents.Construction.nativeBlockComponent_value j iota hsplit A ρ n (labels (v, false)) U
          ((A.abelian.torsionFunctor (q ^ n)).map t.op y))
    exact (congrArg (fun w => Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U w z) hv).mpr hs
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, (congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n (labels (v, false)) T) ha).trans
    (IntrinsicBlockComponents.Construction.nativeBlockComponent_value j iota hsplit A ρ n (labels (v, false)) T y)⟩

include hρ hgood hc in
theorem prescribedKernel_maximal
    (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
    (h : PrescribedKernelOrthogonal j iota hsplit A ρ n s labels H T y) :
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T y.val := by
  refine ⟨y, rfl, fun v => ⟨?_, ?_⟩⟩
  · exact prescribedOrthogonal_chosen_component j iota hsplit A ρ hρ hgood n s labels hc H T y h v (P v)
  · exact prescribedOrthogonal_opposite_component j iota hsplit A ρ hρ n s labels hc H T y h v

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedMaximality.Construction
