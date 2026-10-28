import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedMaximality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedIsotropy

/-! # Prescribed Self Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSelfAnnihilator.Construction

noncomputable section

/-! The exact independently prescribed full kernel is its own
annihilator for the original canonical pairing on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

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
  (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

include hρ hgood hc P in
theorem prescribedFullKernel_selfAnnihilating (T : Over (Spec (.of k)))
    (y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    PrescribedMaximality.Construction.PrescribedKernelOrthogonal j iota hsplit A ρ n s labels H T y ↔
      Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T y.val := by
  constructor
  · exact PrescribedMaximality.Construction.prescribedKernel_maximal j iota hsplit A ρ hρ hgood n s labels hc H T y P
  · intro hy U t x hx
    exact PrescribedIsotropy.Construction.prescribedKernelComponents_isotropic j iota hsplit A ρ n s labels H U x
      ((A.abelian.torsionFunctor (q ^ n)).map t.op y) hρ hc
      (PrescribedNaturality.Construction.prescribedFullKernel_torsion_components j iota hsplit A ρ n s labels H U x hx)
      (fun v => PrescribedNaturality.Construction.prescribedKernelComponentCondition_natural j iota hsplit A ρ n s labels H t y v
        (PrescribedNaturality.Construction.prescribedFullKernel_torsion_components j iota hsplit A ρ n s labels H T y hy v))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSelfAnnihilator.Construction
