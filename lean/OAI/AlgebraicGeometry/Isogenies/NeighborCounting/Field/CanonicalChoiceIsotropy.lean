import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalAlternation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCanonicalAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel

/-! # Canonical Choice Isotropy -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalChoiceIsotropy

noncomputable section

/-! The original complete chosen/opposite kernel is maximally isotropic
over its actual characteristic-zero field. Its pairing properties come
from the original positive polarization and Rosati action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalAlternation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCanonicalAdjoints

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [CharZero k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hdegree : q.Coprime ((∏ i, δ i) ^ 2))
  (n s : ℕ) (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (M : Fin s → Type) [∀ i, AddCommGroup (M i)]
  [∀ i, Module (ZMod (q ^ n)) (M i)] [∀ i, Finite (M i)]
  {P : Over (Spec (.of k))}
  (U : ∀ i, AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A.abelian.scheme (q ^ n) (M i)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels i) P)

include hρ hdegree hlabels in
theorem canonicalChoiceKernel_self_annihilating :
    let b := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization
      (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))
      (AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (q ^ n) s M (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels)
        (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A.abelian ρ n s labels)
        (AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit A.abelian ρ n s labels b) U)
    b.relativeAnnihilator H = H := by
  apply AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction.l45_choice_kernel_self_annihilating_from_perfect_source j iota hsplit A.abelian ρ
    n s labels _ (𝟙 (Spec (.of k))) hlabels M U
  · exact AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing_isPerfect A.abelian A.dual A.polarization
      (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) (hdegree.pow_left n)
  · exact CanonicalAlternation.reducedFieldPairing_alternating A.abelian A.dual A.polarization
      (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
  · exact ReducedCanonicalAdjoints.reducedNativePolarizationPairing_coefficient_adjoint A ρ hρ
      (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalChoiceIsotropy
