import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OrdinaryFamilies
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Nondegeneracy
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CompactKernelComponents
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

/-! # One Step Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OneStepKernel

noncomputable section

/-! Literal compact restrictions of the actual canonical one-step
quotient. Both chosen and opposite restrictions are derived from its
independent full-kernel prescription. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Kernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OrdinaryFamilies.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CompactKernelComponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties.IntrinsicFamily OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Nondegeneracy

def mapKernelFamily {S : Scheme} {A C P : Over S} [GrpObj A] [GrpObj C]
    (f : A ⟶ C) [IsMonHom f] : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P where
  points T _ := (IsMonHom.monoidHom f T).ker
  naturality := by
    intro T U t p a ha
    change (t ≫ a) ≫ f = 1
    change a ≫ f = 1 at ha
    rw [Category.assoc, ha, MonObj.comp_one]

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ)) (compact : Fin s → Bool)
variable (H0 : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (0, false)) n))
variable (C0 : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v.succ, false)) n))
variable (hC0 : ∀ (v : Fin s) (T : Over (Spec (.of k)))
  (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v.succ, false)) n).X),
  (∃ h : T ⟶ (C0 v).group.X, h ≫ (C0 v).inclusion.hom.hom = a) ↔ if compact v then True else a = 1)
variable {C : Over (Spec (.of k))} [GrpObj C] (f : A.abelian.scheme ⟶ C) [IsMonHom f]
variable (hf : ∀ (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme),
  a ≫ f = 1 ↔ AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n (s + 1) labels
    (OrdinaryFamilies.Ordinary.canonicalChosenFamily j iota hsplit A ρ n s labels H0 C0) T a)

include hC0 hf in
omit [NumberField.IsCMField E] in
theorem canonical_map_kernel_iff (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme) :
    a ≫ f = 1 ↔ a ∈ (Kernel.Models.multiplierFullKernel (q ^ n)
      (Intrinsic.KernelComparison.chosenProjector j iota hsplit A ρ n (s + 1) labels)
      (Intrinsic.KernelComparison.oppositeProjector j iota hsplit A ρ n (s + 1) labels)
      (fun v => CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n (labels (v, false)) (labels (v, true)))
      0 (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit A ρ n s labels H0)).points T (toUnit T) := by
  have h := (Kernel.prescribed_full_family_eq j iota hsplit A ρ n (s + 1) labels
    (OrdinaryFamilies.Ordinary.canonicalChosenFamily j iota hsplit A ρ n s labels H0 C0)
    (mapKernelFamily (P := 𝟙_ (Over (Spec (.of k)))) f) (fun U _ a => hf U a)).trans
    (OrdinaryFamilies.Ordinary.canonical_ordinary_full_family j iota hsplit A ρ n s labels compact H0 C0 hC0)
  change a ∈ (mapKernelFamily f).points T (toUnit T) ↔ _
  rw [h]

include hC0 hf in
omit [NumberField.IsCMField E] in
theorem canonical_one_step_compact_chosen {m : ℕ} (hnm : n ≤ m) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit m (labels (v.succ, false))) = a) :
    a ≫ f = 1 ↔ if compact v then a ^ (q ^ n) = 1 else a = 1 := by
  rw [canonical_map_kernel_iff j iota hsplit A ρ n s labels compact H0 C0 hC0 f hf]
  have hp := Intrinsic.ChosenFamilyProperties.IntrinsicFamily.original_block_family_bound (P := 𝟙_ (Over (Spec (.of k))))
    j iota hsplit A.abelian ρ n (labels (0, false)) H0.inclusion
  exact Intrinsic.CompactKernelComponents.compact_chosen_higher j iota hsplit A.abelian ρ (Intrinsic.KernelLabels.nativeKernelLabels labels) hnm
    (fun w => CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n (labels (w, false)) (labels (w, true)))
    0 (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit A ρ n s labels H0)
    hp.1 hp.2 v.succ (Fin.succ_ne_zero v) T (toUnit T) a ha

include hC0 hf in
theorem canonical_one_step_compact_opposite (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (hdegree : q.Coprime (∏ i, δ i))
    (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
    {m : ℕ} (hnm : n ≤ m) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit m (labels (v.succ, true))) = a) :
    a ≫ f = 1 ↔ if compact v then a = 1 else a ^ (q ^ n) = 1 := by
  rw [canonical_map_kernel_iff j iota hsplit A ρ n s labels compact H0 C0 hC0 f hf]
  have hp := Intrinsic.ChosenFamilyProperties.IntrinsicFamily.original_block_family_bound (P := 𝟙_ (Over (Spec (.of k))))
    j iota hsplit A.abelian ρ n (labels (0, false)) H0.inclusion
  exact Intrinsic.CompactKernelComponents.compact_opposite_higher j iota hsplit A.abelian ρ (Intrinsic.KernelLabels.nativeKernelLabels labels) hnm
    (fun w => CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n (labels (w, false)) (labels (w, true)))
    0 (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit A ρ n s labels H0)
    hp.1 hp.2 v.succ (Fin.succ_ne_zero v)
    (Nondegeneracy.canonical_coefficient_zero_double j iota hsplit A ρ hρ hdegree n
      (labels (v.succ, false)) (labels (v.succ, true)) (hc v.succ)) T (toUnit T) a ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OneStepKernel
