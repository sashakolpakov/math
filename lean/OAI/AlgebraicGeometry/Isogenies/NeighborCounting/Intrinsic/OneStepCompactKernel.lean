import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveRestriction
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CompactKernelComponents
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoefficientNondegeneracy

/-! # One Step Compact Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepCompactKernel

noncomputable section

/-! Compute all compact restrictions directly from the original
one-step complete ordinary kernel. The opposite pairing's required
nondegeneracy is proved from its native Cartier construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties.IntrinsicFamily OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CompactKernelComponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoefficientNondegeneracy

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
variable {C : Over (Spec (.of k))} [GrpObj C] (f : PEL.abelian.scheme ⟶ C)
variable (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f
  (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n (s + 1) labels P
    (OrdinaryKernelFamilies.IntrinsicOrdinary.ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) hdual))

include hf in
theorem native_one_step_kernel_iff (T : Over (Spec (.of k))) (a : T ⟶ PEL.abelian.scheme) :
    a ≫ f = 1 ↔ a ∈ (Kernel.Models.multiplierFullKernel (q ^ n)
      (KernelComparison.chosenProjector j iota hsplit PEL ρ n (s + 1) labels)
      (KernelComparison.oppositeProjector j iota hsplit PEL ρ n (s + 1) labels)
      (KernelComparison.coefficientPairing j iota hsplit PEL ρ n (s + 1) labels P hdual)
      0 (OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact)
      (OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit PEL ρ n s labels H0)).points T (toUnit T) := by
  rw [← OrdinaryKernelFamilies.IntrinsicOrdinary.ordinary_full_kernel_family j iota hsplit PEL ρ n s labels compact e H0 P hdual]
  constructor
  · intro ha
    obtain ⟨b, hb, _⟩ := (hf T a).mp ha
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    change b ≫ AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n (s + 1) labels P
      (OrdinaryKernelFamilies.IntrinsicOrdinary.ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) hdual = a at hb
    rw [← hb, Category.assoc, AbelianScheme.FrobeniusKernel.Prescribed.Construction.prescribedKernel_kills f _ hf, MonObj.comp_one]

include hf in
theorem native_one_step_compact_chosen {m : ℕ} (hnm : n ≤ m) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ PEL.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit m (labels (v.succ, false))) = a) :
    a ≫ f = 1 ↔ if compact v then a ^ (q ^ n) = 1 else a = 1 := by
  rw [native_one_step_kernel_iff j iota hsplit PEL ρ n s labels compact e H0 P hdual f hf]
  have hp := ChosenFamilyProperties.IntrinsicFamily.original_block_family_bound (P := 𝟙_ (Over (Spec (.of k))))
    j iota hsplit PEL.abelian ρ n (labels (0, false)) H0.inclusion
  exact CompactKernelComponents.compact_chosen_higher j iota hsplit PEL.abelian ρ (KernelLabels.nativeKernelLabels labels)
    hnm (KernelComparison.coefficientPairing j iota hsplit PEL ρ n (s + 1) labels P hdual)
    0 (OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit PEL ρ n s labels H0)
    hp.1 hp.2 v.succ (Fin.succ_ne_zero v) T (toUnit T) a ha

include hf in
theorem native_one_step_compact_opposite {m : ℕ} (hnm : n ≤ m) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ PEL.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit m (labels (v.succ, true))) = a) :
    a ≫ f = 1 ↔ if compact v then a = 1 else a ^ (q ^ n) = 1 := by
  rw [native_one_step_kernel_iff j iota hsplit PEL ρ n s labels compact e H0 P hdual f hf]
  have hp := ChosenFamilyProperties.IntrinsicFamily.original_block_family_bound (P := 𝟙_ (Over (Spec (.of k))))
    j iota hsplit PEL.abelian ρ n (labels (0, false)) H0.inclusion
  exact CompactKernelComponents.compact_opposite_higher j iota hsplit PEL.abelian ρ (KernelLabels.nativeKernelLabels labels)
    hnm (KernelComparison.coefficientPairing j iota hsplit PEL ρ n (s + 1) labels P hdual)
    0 (OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit PEL ρ n s labels H0)
    hp.1 hp.2 v.succ (Fin.succ_ne_zero v)
    (CoefficientNondegeneracy.coefficient_pairing_zero_double j iota hsplit PEL ρ n (s + 1) labels P hdual v.succ)
    T (toUnit T) a ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepCompactKernel
