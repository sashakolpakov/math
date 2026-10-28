import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointAdjoints
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ConjugateProjectors

/-! # Reference Point Projectors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointProjectors.Construction

noncomputable section

/-! The actual coefficient projectors are complete and orthogonal on
every torsion-point group, and conjugate projectors are adjoint for the
original canonical polarization pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (n : ℕ) (T : Over (Spec (.of k)))

def originalPointProjector (τ : Gal(E/ℚ)) :
    (A.abelian.torsionFunctor (q ^ n)).obj (.op T) →*
      (A.abelian.torsionFunctor (q ^ n)).obj (.op T) :=
  ((PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian A.abelian (ρ.map (j.projector iota hsplit n τ)) (q ^ n)).app (.op T)).hom

omit [NumberField.IsCMField E] [IsAlgClosed k] in
theorem originalPointProjector_prescribed (τ : Gal(E/ℚ))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    originalPointProjector j iota hsplit A ρ n T τ x =
      Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x := rfl

omit [NumberField.IsCMField E] [IsAlgClosed k] in
theorem originalPointProjectors_orthogonal (τ υ : Gal(E/ℚ)) (h : τ ≠ υ)
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    originalPointProjector j iota hsplit A ρ n T τ
      (originalPointProjector j iota hsplit A ρ n T υ x) = 1 := by
  apply Subtype.ext
  exact PELModuli.CMPoints.BlockDecomposition.projector_orthogonal_on_torsion j iota hsplit A.abelian ρ n υ τ h.symm T x.val x.property

omit [NumberField.IsCMField E] [IsAlgClosed k] in
theorem originalPointProjectors_complete
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    (∏ τ : Gal(E/ℚ), originalPointProjector j iota hsplit A ρ n T τ x) = x := by
  apply Subtype.ext
  change (A.abelian.torsionPoints (q ^ n) T).subtype
    (∏ τ : Gal(E/ℚ), originalPointProjector j iota hsplit A ρ n T τ x) = x.val
  exact (map_prod (A.abelian.torsionPoints (q ^ n) T).subtype
    (fun τ : Gal(E/ℚ) => show A.abelian.torsionPoints (q ^ n) T from
      originalPointProjector j iota hsplit A ρ n T τ x) Finset.univ).trans
    (PELModuli.CMPoints.BlockDecomposition.torsion_projectors_sum j iota hsplit A.abelian ρ n T x.val x.property)

theorem originalPointProjectors_adjoint (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (τ : Gal(E/ℚ)) (x y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    ReferencePointBicharacter.Construction.originalPointBicharacter A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
      (originalPointProjector j iota hsplit A ρ n T τ x) y =
    ReferencePointBicharacter.Construction.originalPointBicharacter A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T x
      (originalPointProjector j iota hsplit A ρ n T (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) y) := by
  rw [ReferencePointBicharacter.Construction.originalPointBicharacter_value, ReferencePointBicharacter.Construction.originalPointBicharacter_value]
  have ha := ReferencePointAdjoints.Construction.originalPointPairing_coefficient_adjoint A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
    ρ hρ (j.projector iota hsplit n τ) T x y
  have hp := ConcreteCategory.congr_hom (NatTrans.congr_app
    (PELModuli.CMPoints.ConjugateProjectors.conjugate_projector_on_torsion j iota hsplit A.abelian ρ n τ) (.op T)) y
  exact ha.trans (congrArg (DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A (q ^ n)
    (pow_pos (Fact.out : q.Prime).pos n) T x) hp)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointProjectors.Construction
