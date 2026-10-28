import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors

/-! # Integral Kernel Parameter Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralKernelParameterChange

noncomputable section

/-! The integral complete kernel uses the same active finite-flat
subgroup at every parameter. Its full chosen and opposite families
commute with changing that parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

variable {S : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S] {g N s : ℕ} {δ : Fin g → ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (n : ℕ) (active : Fin s)
  (multiplicative : Fin s → Bool) {P Q : Over S} (b : Q ⟶ P)
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (ρ.map (j.projector iota hsplit 1 (labels (.inl active))))))

omit [NumberField.IsCMField E] in
theorem integralCanonicalFullKernel_parameter_baseChange :
    (IntegralCanonicalNeighbors.integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative P H).baseChange b =
      IntegralCanonicalNeighbors.integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative Q H := by
  unfold IntegralCanonicalNeighbors.integralCanonicalFullKernel Kernel.Models.multiplierFullKernel
  exact Kernel.Base.fullKernel_baseChange _ _ _ _ _ active multiplicative _ b

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralKernelParameterChange
