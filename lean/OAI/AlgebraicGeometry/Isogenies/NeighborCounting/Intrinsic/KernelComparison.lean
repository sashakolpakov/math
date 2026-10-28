import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelPoints
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OppositeFamily
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeBlockTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

/-! # Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison

noncomputable section

/-! Compare the independently constructed FrobeniusKernel complete kernel with
the NeighborCounting chosen/annihilator construction in the actual coefficient
torsion blocks. The pairing is transported from the original source
Cartier identification; no complete-kernel identification is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelPoints OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OppositeFamily.IntrinsicFamily OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeCartierComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeBlockTransport

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (P : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of k)
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

abbrev chosenProjector (v : Fin s) := ρ.map (j.projector iota hsplit n (labels (v, false)))
abbrev oppositeProjector (v : Fin s) := ρ.map (j.projector iota hsplit n (labels (v, true)))

def nativeBlockComparison (τ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≅
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ τ n).X :=
  (Grp.forget _).mapIso
    (CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit PEL.abelian ρ n τ)

instance nativeBlockComparison_isMonHom (τ : Gal(E/ℚ)) :
    IsMonHom (nativeBlockComparison j iota hsplit PEL ρ n τ).hom := by
  exact inferInstanceAs (IsMonHom
    (CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit PEL.abelian ρ n τ).hom.hom.hom)

theorem nativeBlockComparison_inclusion (τ : Gal(E/ℚ)) :
    (nativeBlockComparison j iota hsplit PEL ρ n τ).hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n τ =
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) :=
  CMPointsBlockComparison.nativeCMPointsBlockGroupIso_inclusion j iota hsplit PEL.abelian ρ n τ

def coefficientPairing (v : Fin s) : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (chosenProjector j iota hsplit PEL ρ n s labels v))
    (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (oppositeProjector j iota hsplit PEL ρ n s labels v))
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  (OppositeCartierComparison.oppositePairing (P v) (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45PairingAtLevel j iota hsplit PEL ρ
    (labels (v, false)) (labels (v, true)) (hdual v) n (P v))).restrict
      (nativeBlockComparison j iota hsplit PEL ρ n (labels (v, false))).hom
      (nativeBlockComparison j iota hsplit PEL ρ n (labels (v, true))).hom

theorem native_opposite_comparison {X : Over (Spec (.of k))} (v : Fin s) :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel (q ^ n)
      (chosenProjector j iota hsplit PEL ρ n s labels v)
      (oppositeProjector j iota hsplit PEL ρ n s labels v)
      (coefficientPairing j iota hsplit PEL ρ n s labels P hdual v)
      (Kernel.Base.fixedKernelFamily (P := X) (KernelPoints.chosenAmbientInclusion j iota hsplit PEL ρ n s labels H v)) =
        Kernel.Base.fixedKernelFamily (P := X)
          (KernelPoints.oppositeAmbientInclusion j iota hsplit PEL ρ n s labels P H hdual v) := by
  unfold AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel coefficientPairing
  rw [OppositeBlockTransport.opposite_image_block_iso _ _ _
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, false)))
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (chosenProjector j iota hsplit PEL ρ n s labels v))
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, true)))
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (oppositeProjector j iota hsplit PEL ρ n s labels v))
    (nativeBlockComparison_inclusion j iota hsplit PEL ρ n (labels (v, false)))
    (nativeBlockComparison_inclusion j iota hsplit PEL ρ n (labels (v, true)))]
  have : Mono (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, false))) := by
    have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, false))).left :=
      PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed PEL.abelian ρ _ _
    apply Over.mono_of_mono_left
  exact OppositeFamily.IntrinsicFamily.native_opposite_family (P v) (H v).coordinates (H v).inclusion
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45PairingAtLevel j iota hsplit PEL ρ (labels (v, false)) (labels (v, true)) (hdual v) n (P v))
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, false)))
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (v, true)))

theorem native_full_kernel_pairing {X : Over (Spec (.of k))} :
    Kernel.Base.fixedKernelFamily (P := X)
      (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct
        (Kernel.Base.fixedKernelFamily (KernelPoints.chosenAmbientInclusion j iota hsplit PEL ρ n s labels H v))
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel (q ^ n)
          (chosenProjector j iota hsplit PEL ρ n s labels v)
          (oppositeProjector j iota hsplit PEL ρ n s labels v)
          (coefficientPairing j iota hsplit PEL ρ n s labels P hdual v)
          (Kernel.Base.fixedKernelFamily (KernelPoints.chosenAmbientInclusion j iota hsplit PEL ρ n s labels H v)))) := by
  rw [KernelPoints.native_full_kernel_family]
  congr 1
  funext v
  rw [native_opposite_comparison]

/-- Once the individual chosen subgroups have been computed, the entire
native kernel follows, including its independently defined opposites. -/
theorem native_full_kernel_of_chosen_families {X : Over (Spec (.of k))}
    (active : Fin s) (multiplicative : Fin s → Bool)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup PEL.abelian.scheme X)
    (hchosen : ∀ v, Kernel.Base.fixedKernelFamily
      (KernelPoints.chosenAmbientInclusion j iota hsplit PEL ρ n s labels H v) =
        Kernel.Base.chosenKernel
          (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (chosenProjector j iota hsplit PEL ρ n s labels w))
          (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (chosenProjector j iota hsplit PEL ρ n s labels w))
          active multiplicative F v) :
    Kernel.Base.fixedKernelFamily
      (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n s labels P H hdual) =
      Kernel.Models.multiplierFullKernel (q ^ n)
        (chosenProjector j iota hsplit PEL ρ n s labels)
        (oppositeProjector j iota hsplit PEL ρ n s labels)
        (coefficientPairing j iota hsplit PEL ρ n s labels P hdual) active multiplicative F := by
  rw [native_full_kernel_pairing]
  unfold Kernel.Models.multiplierFullKernel Kernel.Base.fullKernel
  congr 1
  funext v
  rw [hchosen v]
  rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison
