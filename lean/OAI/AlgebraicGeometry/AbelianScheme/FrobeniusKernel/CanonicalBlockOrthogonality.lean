import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointProjectors
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointAlternation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockProjectorPoints

/-! # Canonical Block Orthogonality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockOrthogonality.Construction

noncomputable section

/-! Canonical orthogonality is symmetric, and a supported block point
tests only the conjugate component of the second point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem canonicalTorsionOrthogonal_iff_bicharacter (m : ℕ) (hm : 0 < m)
    (T : Over (Spec (.of k))) (x y : (A.abelian.torsionFunctor m).obj (.op T)) :
    Prescription.Construction.canonicalTorsionOrthogonal A m hm T x y ↔ ReferencePointBicharacter.Construction.originalPointBicharacter A m hm T x y = 1 :=
  (DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value A m hm T x y).trans
    (iff_of_eq (congrArg (fun z => z = 1) (ReferencePointBicharacter.Construction.originalPointBicharacter_value A m hm T x y))).symm

theorem canonicalTorsionOrthogonal_symm (m : ℕ) (hm : 0 < m)
    (T : Over (Spec (.of k))) (x y : (A.abelian.torsionFunctor m).obj (.op T))
    (h : Prescription.Construction.canonicalTorsionOrthogonal A m hm T x y) : Prescription.Construction.canonicalTorsionOrthogonal A m hm T y x := by
  have hx := (canonicalTorsionOrthogonal_iff_bicharacter A m hm T x y).mp h
  exact (canonicalTorsionOrthogonal_iff_bicharacter A m hm T y x).mpr
    ((ReferencePointAlternation.Construction.originalPointBicharacter_skew A m hm T x y).trans ((congrArg Inv.inv hx).trans inv_one))

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (n : ℕ) (τ : Gal(E/ℚ))
  (T : Over (Spec (.of k))) (x : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X)
  (y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))

include hρ in
theorem canonicalBlockOrthogonal_project_target :
    Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
      (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T x) y ↔
    Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
      (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T x)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) T y) := by
  let z := CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T x
  let b := ReferencePointBicharacter.Construction.originalPointBicharacter A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
  have hfix := (ReferencePointProjectors.Construction.originalPointProjector_prescribed j iota hsplit A ρ n T τ z).trans
    (CanonicalBlockProjectorPoints.Construction.canonicalOriginalBlockPoint_component_self A j iota hsplit ρ n τ T x)
  have hv : b z y = b z (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) T y) :=
    (congrArg (fun a => b a y) hfix).symm.trans
      ((ReferencePointProjectors.Construction.originalPointProjectors_adjoint j iota hsplit A ρ n T hρ τ z y).trans
        (congrArg (b z) (ReferencePointProjectors.Construction.originalPointProjector_prescribed j iota hsplit A ρ n T
          (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) y)))
  exact (canonicalTorsionOrthogonal_iff_bicharacter A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T z y).trans
    ((iff_of_eq (congrArg (fun a => a = 1) hv)).trans
      (canonicalTorsionOrthogonal_iff_bicharacter A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T z _).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockOrthogonality.Construction
