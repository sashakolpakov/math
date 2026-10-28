import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents

/-! # One Step Kernel Recovery -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepKernelRecovery

noncomputable section

/-! Recover the actual one-step active subgroup from the independently
constructed complete ordinary kernel. Higher-level coefficient support
does not introduce extra sections; its reduction is proved from the
original complete kernel's torsion bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties.IntrinsicFamily OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.AllKernelComponents.IntrinsicChosenRecovery

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (compact : Fin s → Bool)
variable (e : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n) q n
    (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights compact v) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights compact v))
variable (H0 : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (0, false)) n))
variable (P : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of k)
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin (s + 1), PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

theorem native_one_step_active_factor {C : Over (Spec (.of k))} [GrpObj C]
    (f : PEL.abelian.scheme ⟶ C)
    (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f
      (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n (s + 1) labels P
        (OrdinaryKernelFamilies.IntrinsicOrdinary.ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) hdual))
    {m : ℕ} (hnm : n ≤ m) (T : Over (Spec (.of k))) (a : T ⟶ PEL.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit m (labels (0, false))) = a)
    (hk : a ≫ f = 1) :
    ∃ h : T ⟶ H0.group.X,
      h ≫ (H0.inclusion.hom.hom ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (0, false))) = a := by
  have hmem : a ∈ (Kernel.Base.fixedKernelFamily
      (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n (s + 1) labels P
        (OrdinaryKernelFamilies.IntrinsicOrdinary.ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) hdual)).points T (toUnit T) := by
    obtain ⟨b, hb, _⟩ := (hf T a).mp hk
    exact ⟨b, hb⟩
  rw [OrdinaryKernelFamilies.IntrinsicOrdinary.ordinary_full_kernel_family] at hmem
  have hp := ChosenFamilyProperties.IntrinsicFamily.original_block_family_bound (P := 𝟙_ (Over (Spec (.of k))))
    j iota hsplit PEL.abelian ρ n (labels (0, false)) H0.inclusion
  exact AllKernelComponents.IntrinsicChosenRecovery.active_factor_at_higher_projector j iota hsplit PEL.abelian ρ (KernelLabels.nativeKernelLabels labels)
    hnm (KernelComparison.coefficientPairing j iota hsplit PEL ρ n (s + 1) labels P hdual)
    0 (OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit PEL ρ n s labels H0)
    hp.1 hp.2 _ rfl T (toUnit T) a ha hmem

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepKernelRecovery
