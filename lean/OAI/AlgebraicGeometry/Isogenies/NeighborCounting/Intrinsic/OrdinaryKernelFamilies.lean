import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChosenFamilies
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsYZQuotients

/-! # Ordinary Kernel Families -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary

noncomputable section

/-! Compute the compact parts of the original native ordinary family.
The active subgroup is retained with its given original inclusion;
every compact part and every opposite part is derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelPoints OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChosenFamilies OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport.Family

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

def compactPrescription : Fin (s + 1) → Bool := Fin.cases false compact

def ordinaryChosenFamily : ∀ v : Fin (s + 1),
    AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n) :=
  Fin.cases H0 (fun v => AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e v.succ))

abbrev activeChosenFamily {X : Over (Spec (.of k))} : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup PEL.abelian.scheme X :=
  Kernel.Base.fixedKernelFamily (H0.inclusion.hom.hom ≫
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (0, false)))

theorem ordinary_chosen_prescription {X : Over (Spec (.of k))} (v : Fin (s + 1)) :
    Kernel.Base.fixedKernelFamily (P := X)
      (KernelPoints.chosenAmbientInclusion j iota hsplit PEL ρ n (s + 1) labels
        (ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) v) =
      Kernel.Base.chosenKernel
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (KernelComparison.chosenProjector j iota hsplit PEL ρ n (s + 1) labels w))
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n)
          (KernelComparison.chosenProjector j iota hsplit PEL ρ n (s + 1) labels w))
        0 (compactPrescription s compact) (activeChosenFamily j iota hsplit PEL ρ n s labels H0) v := by
  classical
  refine Fin.cases ?_ (fun w => ?_) v
  · rw [Kernel.Base.chosenKernel, ite_eq_left rfl]
    rfl
  · rw [Kernel.Base.chosenKernel, ite_eq_right (Fin.succ_ne_zero w)]
    change Kernel.Base.fixedKernelFamily
      ((AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e w.succ)).inclusion.hom.hom ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (w.succ, false))) =
      if compact w then Kernel.Base.fixedKernelFamily
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n (labels (w.succ, false)))))
      else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup
    have hb := Kernel.FamilyTransport.Family.fixed_iso (P := X)
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n (labels (w.succ, false)))))
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (w.succ, false)))
      (KernelComparison.nativeBlockComparison j iota hsplit PEL ρ n (labels (w.succ, false)))
      (KernelComparison.nativeBlockComparison_inclusion j iota hsplit PEL ρ n (labels (w.succ, false)))
    rw [hb]
    exact CompactChosenFamilies.compact_chosen_family _ (compact w) (e w.succ)

variable (P : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of k)
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin (s + 1), PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

theorem ordinary_full_kernel_family {X : Over (Spec (.of k))} :
    Kernel.Base.fixedKernelFamily (P := X)
      (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n (s + 1) labels P
        (ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) hdual) =
      Kernel.Models.multiplierFullKernel (q ^ n)
        (KernelComparison.chosenProjector j iota hsplit PEL ρ n (s + 1) labels)
        (KernelComparison.oppositeProjector j iota hsplit PEL ρ n (s + 1) labels)
        (KernelComparison.coefficientPairing j iota hsplit PEL ρ n (s + 1) labels P hdual)
        0 (compactPrescription s compact) (activeChosenFamily j iota hsplit PEL ρ n s labels H0) :=
  KernelComparison.native_full_kernel_of_chosen_families j iota hsplit PEL ρ n (s + 1) labels P
    (ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) hdual
    0 (compactPrescription s compact) _
    (ordinary_chosen_prescription j iota hsplit PEL ρ n s labels compact e H0)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary
