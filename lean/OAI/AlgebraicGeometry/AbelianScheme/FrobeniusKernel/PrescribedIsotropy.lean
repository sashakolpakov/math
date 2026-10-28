import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointSplitFormula
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoints

/-! # Prescribed Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedIsotropy.Construction

noncomputable section

/-! The independent chosen/annihilator prescription is isotropic for
the original canonical pairing on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
  (T : Over (Spec (.of k)))
  (x y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))

omit [NumberField.IsCMField E] in
theorem prescribedComponent_cross_orthogonal (v : Fin s)
    (hx : CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T x v)
    (hy : CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T y v) :
    Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, false)) T x)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) T y) := by
  obtain ⟨a, ha⟩ := hx.1
  have hid : (A.abelian.torsionFunctor (q ^ n)).map (𝟙 T).op y = y :=
    ConcreteCategory.congr_hom ((A.abelian.torsionFunctor (q ^ n)).map_id (.op T)) y
  have hp := congrArg (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) T) hid
  exact (congrArg₂ (Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n)
    (pow_pos (Fact.out : q.Prime).pos n) T) ha hp).mp (hy.2 T (𝟙 T) a)

omit [NumberField.IsCMField E] in
theorem prescribedComponent_cross_value (v : Fin s)
    (hx : CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T x v)
    (hy : CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T y v) :
    ReferencePointBicharacter.Construction.originalPointBicharacter A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, false)) T x)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) T y) = 1 :=
  (ReferencePointBicharacter.Construction.originalPointBicharacter_value A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T _ _).trans
    ((DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T _ _).mp
      (prescribedComponent_cross_orthogonal j iota hsplit A ρ n s labels H T x y v hx hy))

theorem prescribedKernelComponents_isotropic
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
    (hx : ∀ v, CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T x v)
    (hy : ∀ v, CanonicalPoints.Construction.prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T y v) :
    Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T x y := by
  apply (DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T x y).mpr
  refine (ReferencePointBicharacter.Construction.originalPointBicharacter_value A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T x y).symm.trans ?_
  refine (ReferencePointSplitFormula.Construction.originalPointPairing_split_formula j iota hsplit A ρ hρ n s labels hc T x y).trans ?_
  apply Finset.prod_eq_one
  intro v _
  rw [prescribedComponent_cross_value j iota hsplit A ρ n s labels H T x y v (hx v) (hy v),
    prescribedComponent_cross_value j iota hsplit A ρ n s labels H T y x v (hy v) (hx v), one_div_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedIsotropy.Construction
