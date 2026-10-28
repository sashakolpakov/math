import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.MixedActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantActiveInclusions
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenSourceIso

/-! # Equivariant Frobenius Z Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusZKernel

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
theorem equivariant_frobenius_Z_active_kernel {C : Over (Spec (.of k))} [GrpObj C]
    (g : PB.abelian.scheme ⟶ C)
    (hg : ∀ (T : Over (Spec (.of k))) (z : T ⟶ PB.abelian.scheme), z ≫ g = 1 ↔
      AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit PB σ 2 (s + 1) labels
        (Fin.cases (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota hsplit PB σ τ eB) C0) T z)
    {n : ℕ} (hn : 2 ≤ n) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PA.abelian).hom ≫ c.abelian.hom ≫ g)
      (Intrinsic.BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit PA.abelian ρ
        (Nat.le_trans (show 1 ≤ 2 by decide) hn) τ) := by
  let H0 := AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota hsplit PB σ τ eB
  let H : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PB σ (labels (v, false)) 2) := Fin.cases H0 C0
  let i := H0.inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PB.abelian σ 2 τ
  let ein := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PB.abelian σ 1 τ
  have hi : i = ein := AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ActivePlaneAtLevelTwo_inclusion j iota hsplit PB σ τ eB
  have hz := PrescribedMapKernel.prescribed_map_chosen_killed j iota hsplit PB σ 2 (s + 1)
    labels H g hg 0 H0.group.X (𝟙 _)
  have hik : i ≫ g = 1 := (congrArg (fun z => z ≫ g) (Category.id_comp i)).symm.trans hz
  have heink : ein ≫ g = 1 := (congrArg (fun z => z ≫ g) hi.symm).trans hik
  have hp := EquivariantActiveInclusions.active_plane_ambient_source_transport j iota hsplit k AF PB.abelian ρF σ c τ ep
  have hplane : PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k PA.abelian ρ τ eF ≫ c.abelian.hom = ein :=
    (Category.assoc _ _ _).trans hp
  have hplanek : PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k PA.abelian ρ τ eF ≫ (c.abelian.hom ≫ g) = 1 :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ g) hplane).trans heink)
  apply ExhaustiveFrobeniusLine.Plane.exhaustive_frobenius_plane
    j iota hsplit k PA.abelian ρ τ e eF (c.abelian.hom ≫ g)
    (Nat.le_trans (show 1 ≤ 2 by decide) hn) hplanek
  intro T z hz hk
  have hz' : (z ≫ c.abelian.hom) ≫ σ.map (j.projector iota hsplit n τ) = z ≫ c.abelian.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => z ≫ f) (c.action (j.projector iota hsplit n τ)).symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ c.abelian.hom) hz)))
  obtain ⟨w, hw⟩ := PrescribedMapKernel.prescribed_map_chosen_factor j iota hsplit PB σ 2 (s + 1) labels H g hg hn
    0 T (z ≫ c.abelian.hom) hz' ((Category.assoc _ _ _).trans hk)
  refine ⟨w, ?_⟩
  apply (cancel_mono c.abelian.hom).mp
  exact (Category.assoc _ _ _).trans ((congrArg (fun f => w ≫ f) hplane).trans
    ((congrArg (fun f => w ≫ f) hi.symm).trans hw))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantFrobeniusZKernel
