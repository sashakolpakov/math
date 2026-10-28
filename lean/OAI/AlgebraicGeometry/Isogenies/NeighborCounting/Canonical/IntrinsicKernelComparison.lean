import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Kernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection

/-! # Intrinsic Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.IntrinsicKernelComparison.Intrinsic

noncomputable section

/-! Compare the complete canonical FrobeniusKernel kernel with the native
chosen/annihilator family used in the original IsogenyQuotient neighbor counts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Kernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.BlockPairing OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeBlockTransport OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport.Family

private theorem pairing_ext {S : Scheme} {B C W : Over S} [GrpObj B] [GrpObj C] [GrpObj W]
    (e f : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := B) (B := C) (W := W))
    (h : ∀ (T : Over S) (x : T ⟶ B) (y : T ⟶ C), e.pairValue x y = f.pairValue x y) : e = f := by
  have he := h (B ⊗ C) (fst B C) (snd B C)
  simp only [AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.pairValue, lift_fst_snd, Category.id_comp] at he
  obtain ⟨e, _, _, _, _⟩ := e
  obtain ⟨f, _, _, _, _⟩ := f
  cases he
  rfl

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

omit [IsAlgClosed k] in
theorem originalBlockNativeTorsionMap_afterComparison (n : ℕ) (τ : Gal(E/ℚ)) :
    (Intrinsic.KernelComparison.nativeBlockComparison j iota hsplit A ρ n τ).hom ≫
      BlockPairing.originalBlockNativeTorsionMap j iota hsplit A ρ n τ =
      AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ))) := by
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))).mp
  rw [Category.assoc, BlockPairing.originalBlockNativeTorsionMap_inclusion, Intrinsic.KernelComparison.nativeBlockComparison_inclusion]
  rfl

def canonicalNativeBlockPairing (n : ℕ) (τ υ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
      (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ)))
      (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n υ)))
      (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  (BlockPairing.prescribedOriginalBlockPairing j iota hsplit A ρ n τ υ).restrict
    (Intrinsic.KernelComparison.nativeBlockComparison j iota hsplit A ρ n τ).hom
    (Intrinsic.KernelComparison.nativeBlockComparison j iota hsplit A ρ n υ).hom

theorem canonicalNativeBlockPairing_eq_source (n : ℕ) (τ υ : Gal(E/ℚ)) :
    canonicalNativeBlockPairing j iota hsplit A ρ n τ υ =
      CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n τ υ := by
  apply pairing_ext
  intro T x y
  simp only [canonicalNativeBlockPairing, BlockPairing.prescribedOriginalBlockPairing,
    CoefficientPerfection.canonicalCoefficientPairing, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue, Category.assoc,
    originalBlockNativeTorsionMap_afterComparison]

variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

theorem canonical_opposite_native {P : Over (Spec (.of k))} (v : Fin s) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, true)))
      ((BlockPairing.prescribedOriginalBlockPairing j iota hsplit A ρ n
        (labels (v, false)) (labels (v, true))).relativeAnnihilator
          (Kernel.Base.fixedKernelFamily (P := P) (H v).inclusion.hom.hom)) =
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel (q ^ n)
        (Intrinsic.KernelComparison.chosenProjector j iota hsplit A ρ n s labels v)
        (Intrinsic.KernelComparison.oppositeProjector j iota hsplit A ρ n s labels v)
        (CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n (labels (v, false)) (labels (v, true)))
        (Kernel.Base.fixedKernelFamily ((H v).inclusion.hom.hom ≫
          AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false)))) := by
  have : IsClosedImmersion
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false))).left :=
    PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed A.abelian ρ _ _
  have : Mono (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false))) :=
    Over.mono_of_mono_left _
  have he := OppositeBlockTransport.opposite_image_block_iso
    (BlockPairing.prescribedOriginalBlockPairing j iota hsplit A ρ n (labels (v, false)) (labels (v, true)))
    (Intrinsic.KernelComparison.nativeBlockComparison j iota hsplit A ρ n (labels (v, false)))
    (Intrinsic.KernelComparison.nativeBlockComparison j iota hsplit A ρ n (labels (v, true)))
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false)))
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (Intrinsic.KernelComparison.chosenProjector j iota hsplit A ρ n s labels v))
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, true)))
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (Intrinsic.KernelComparison.oppositeProjector j iota hsplit A ρ n s labels v))
    (Intrinsic.KernelComparison.nativeBlockComparison_inclusion j iota hsplit A ρ n (labels (v, false)))
    (Intrinsic.KernelComparison.nativeBlockComparison_inclusion j iota hsplit A ρ n (labels (v, true)))
    (Kernel.Base.fixedKernelFamily (P := P) ((H v).inclusion.hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false))))
  rw [Kernel.FamilyTransport.Family.pullback_fixed_comp] at he
  change AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel (q ^ n)
    (Intrinsic.KernelComparison.chosenProjector j iota hsplit A ρ n s labels v)
    (Intrinsic.KernelComparison.oppositeProjector j iota hsplit A ρ n s labels v)
    (canonicalNativeBlockPairing j iota hsplit A ρ n (labels (v, false)) (labels (v, true))) _ = _ at he
  rw [canonicalNativeBlockPairing_eq_source] at he
  exact he.symm

theorem originalCanonicalFullFamily_native {P : Over (Spec (.of k))} :
    Kernel.originalCanonicalFullFamily (P := P) j iota hsplit A ρ n s labels H =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct
        (Kernel.Base.fixedKernelFamily ((H v).inclusion.hom.hom ≫
          AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false))))
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel (q ^ n)
          (Intrinsic.KernelComparison.chosenProjector j iota hsplit A ρ n s labels v)
          (Intrinsic.KernelComparison.oppositeProjector j iota hsplit A ρ n s labels v)
          (CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n (labels (v, false)) (labels (v, true)))
          (Kernel.Base.fixedKernelFamily ((H v).inclusion.hom.hom ≫
            AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false)))))) := by
  unfold Kernel.originalCanonicalFullFamily
  congr 1
  funext v
  rw [canonical_opposite_native]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.IntrinsicKernelComparison.Intrinsic
