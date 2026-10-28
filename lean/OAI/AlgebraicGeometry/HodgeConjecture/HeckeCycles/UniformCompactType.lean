import OAI.RepresentationTheory.Hecke.UniformCompactType
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

/-! # Uniform Compact Type -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniformCompactType.CM

noncomputable section

/-! The actual prescribed PEL Lie ranks make NeighborCounting's compact types
uniform across ordinary source points. Transport the entire native
reduction output through this proved equality of types. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification OAI.RepresentationTheory.Hecke.UniformCompactType.OrdinaryCharacterIntrinsic

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  (hres : RepresentationTheory.Hecke.ModelBlockCharacters.OrdinaryCharacterIntrinsic.CoefficientResidueSquare D j) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b ρ)
  (X Z : D.OrdinaryPoint → D.OrdinaryPoint) (Y : D.OrdinaryPoint → Multiset D.OrdinaryPoint)

omit [IsFractionRing R L] in
include hres in
theorem reduction_with_fixed_type
    (hred : ∀ (x : D.OrdinaryPoint) (l : Isogenies.NeighborCounting.Lifts.IntegralLift D R b ρ x.val),
      Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) 0
        (Fin.cases false (O.compact x)) hTorsionQuotient hbase X Y Z x l) :
    ∀ (x : D.OrdinaryPoint) (l : Isogenies.NeighborCounting.Lifts.IntegralLift D R b ρ x.val),
      Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) 0
        (RepresentationTheory.Hecke.UniformCompactType.OrdinaryCharacterIntrinsic.prescribedMultiplicativeType P labels) hTorsionQuotient hbase X Y Z x l := by
  intro x l
  exact (RepresentationTheory.Hecke.UniformCompactType.OrdinaryCharacterIntrinsic.ordinary_multiplicative_prescribed D j hsplit labels O hres x) ▸ hred x l

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniformCompactType.CM
