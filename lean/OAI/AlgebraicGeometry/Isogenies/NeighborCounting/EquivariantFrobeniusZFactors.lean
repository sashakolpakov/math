import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusZKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.MixedLineFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.MixedActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantActiveInclusions
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso

/-! # Equivariant Frobenius Z Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusZFactors

noncomputable section

/-! The exhaustive native full-block kernel follows from an independent
Z kernel at any equivariantly identified Frobenius target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedMapKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantActiveInclusions
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HigherChosenSupport

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d N : ℕ} {δ : Fin d → ℕ}
  (PA PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian)
  (c : AbelianScheme.FrobeniusKernel.PolarizedComponents.Construction.EquivariantAbelianIso (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k PA.abelian) PB.abelian
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ) σ)
  (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PA.abelian ρ 1 (labels (0, false))).toGrp)
  (eB : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PB σ (labels (0, false)) 1) q 1 1 2)
  (C0 : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PB σ (labels (v.succ, false)) 2))

local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k PA.abelian
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ
local notation "τ" => labels (0, false)
local notation "ep" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q eB
local notation "eF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso.Construction.frobeniusSourceActiveSplitting j iota hsplit k PA.abelian PB.abelian ρ σ c τ ep

include e in
theorem equivariant_frobenius_Z_active_factor {C : Over (Spec (.of k))} [GrpObj C]
    (g : PB.abelian.scheme ⟶ C)
    (hg : ∀ (T : Over (Spec (.of k))) (z : T ⟶ PB.abelian.scheme), z ≫ g = 1 ↔
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit PB σ 2 (s + 1) labels
        (Fin.cases (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota hsplit PB σ τ eB) C0) T z)
    {n : ℕ} (hn : 2 ≤ n)
    (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme)
    (ha : a ^ (q ^ n) = 1)
    (hp : a ≫ ρ.map (j.projector iota hsplit n τ) = a) :
    type_of% (Intrinsic.BlockFactors.native_full_block_kernel_factor
    j iota hsplit PA.abelian ρ (Nat.le_trans (show 1 ≤ 2 by decide) hn) τ
    ((AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PA.abelian).hom ≫ c.abelian.hom ≫ g)
    (EquivariantFrobeniusZKernel.equivariant_frobenius_Z_active_kernel
      j iota hsplit k PA PB ρ σ c s labels e eB C0 g hg hn) T a ha hp) :=
  Intrinsic.BlockFactors.native_full_block_kernel_factor
    j iota hsplit PA.abelian ρ (Nat.le_trans (show 1 ≤ 2 by decide) hn) τ
    ((AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PA.abelian).hom ≫ c.abelian.hom ≫ g)
    (EquivariantFrobeniusZKernel.equivariant_frobenius_Z_active_kernel
      j iota hsplit k PA PB ρ σ c s labels e eB C0 g hg hn) T a ha hp

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusZFactors
