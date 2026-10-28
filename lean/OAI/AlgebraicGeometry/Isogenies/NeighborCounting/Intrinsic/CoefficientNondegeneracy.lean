import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierNondegeneracy
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison

/-! # Coefficient Nondegeneracy -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoefficientNondegeneracy

noncomputable section

/-! The zero-subgroup double-annihilator identity for the original
native coefficient pairing is derived from actual Cartier characters.
Thus the compact opposite formulas need no extra nondegeneracy premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CartierNondegeneracy

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {d N : ℕ} {δ : Fin d → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (P : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of k)
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

local instance (v : Fin s) (b : Bool) :
    IsCommMonObj (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, b)) n).X :=
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ n (labels (v, b))).comm

theorem coefficient_pairing_zero_double {X : Over (Spec (.of k))} (v : Fin s) :
    (KernelComparison.coefficientPairing j iota hsplit PEL ρ n s labels P hdual v).relativeAnnihilator
      ((KernelComparison.coefficientPairing j iota hsplit PEL ρ n s labels P hdual v).flip.relativeAnnihilator
        (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup
          (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (KernelComparison.oppositeProjector j iota hsplit PEL ρ n s labels v)) (P := X))) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup
        (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (KernelComparison.oppositeProjector j iota hsplit PEL ρ n s labels v)) (P := X) :=
  CartierNondegeneracy.coefficient_annihilator_zero_double (P v)
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45PairingAtLevel j iota hsplit PEL ρ (labels (v, false)) (labels (v, true)) (hdual v) n (P v))
    (KernelComparison.nativeBlockComparison j iota hsplit PEL ρ n (labels (v, false)))
    (KernelComparison.nativeBlockComparison j iota hsplit PEL ρ n (labels (v, true)))

theorem coefficient_opposite_whole {X : Over (Spec (.of k))} (v : Fin s) :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel (q ^ n)
      (KernelComparison.chosenProjector j iota hsplit PEL ρ n s labels v)
      (KernelComparison.oppositeProjector j iota hsplit PEL ρ n s labels v)
      (KernelComparison.coefficientPairing j iota hsplit PEL ρ n s labels P hdual v)
      (Kernel.Base.fixedKernelFamily (P := X) (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n)
        (KernelComparison.chosenProjector j iota hsplit PEL ρ n s labels v))) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (A := PEL.abelian.scheme) (P := X) :=
  CompactOpposites.Kernel.opposite_of_whole _ _ _ _ (coefficient_pairing_zero_double j iota hsplit PEL ρ n s labels P hdual v)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoefficientNondegeneracy
