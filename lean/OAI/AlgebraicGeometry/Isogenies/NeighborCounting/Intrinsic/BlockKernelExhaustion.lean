import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion

/-! # Block Kernel Exhaustion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion

noncomputable section

/-! Embed the original lower coefficient block into higher torsion with
the actual projector at each level. A proved lower-torsion bound on the
ambient kernel makes its lower-block computation exhaustive. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedKernelExhaustion

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable {m n : ℕ} (hmn : m ≤ n) (τ : Gal(E/ℚ))

include hmn in
theorem low_block_fixed_high :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ)) ≫
      σ.map (j.projector iota hsplit n τ) =
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ)) := by
  have h := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ _ (q ^ m)
    (by simpa only [Nat.cast_pow] using ProjectorLevels.projector_level_congruence j iota hsplit hmn τ)
    _ (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ)))
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed _ _)
  exact h.trans (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_supported _ _)

def nativeBlockEmbedding :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (σ.map (j.projector iota hsplit m τ)) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (σ.map (j.projector iota hsplit n τ)) :=
  AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift (q ^ n) (σ.map (j.projector iota hsplit n τ))
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ))) (by
      obtain ⟨c, hc⟩ := pow_dvd_pow q hmn
      rw [hc, pow_mul, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, one_pow])
    (low_block_fixed_high j iota hsplit A σ hmn τ)

theorem nativeBlockEmbedding_inclusion :
    nativeBlockEmbedding j iota hsplit A σ hmn τ ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) =
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ)) :=
  AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _

instance nativeBlockEmbedding_mono : Mono (nativeBlockEmbedding j iota hsplit A σ hmn τ) :=
  mono_of_mono_fac (nativeBlockEmbedding_inclusion j iota hsplit A σ hmn τ)

instance nativeBlockEmbedding_group : IsMonHom (nativeBlockEmbedding j iota hsplit A σ hmn τ) := by
  apply AbelianScheme.IsogenyQuotient.GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)))).mp
    simp only [Category.assoc, nativeBlockEmbedding_inclusion, MonObj.one_comp]
  · intro T a b
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)))).mp
    simp only [Category.assoc, nativeBlockEmbedding_inclusion, MonObj.mul_comp]

variable {C : Over S} [GrpObj C] (f : A.scheme ⟶ C)
variable (hbound : ∀ (T : Over S) (x : T ⟶ A.scheme),
  x ≫ σ.map (j.projector iota hsplit n τ) = x → x ≫ f = 1 → x ^ (q ^ m) = 1)

include hbound in
theorem native_kernel_factors_low (T : Over S)
    (a : T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (σ.map (j.projector iota hsplit n τ)))
    (ha : a ≫ (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) ≫ f) = 1) :
    ∃ z : T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (σ.map (j.projector iota hsplit m τ)),
      z ≫ nativeBlockEmbedding j iota hsplit A σ hmn τ = a := by
  let x := a ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ))
  have hs : x ≫ σ.map (j.projector iota hsplit n τ) = x := by
    rw [Category.assoc, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_supported]
  have hx : x ^ (q ^ m) = 1 := hbound T x hs ((Category.assoc _ _ _).trans ha)
  have hc := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ _ (q ^ m)
    (by simpa only [Nat.cast_pow] using ProjectorLevels.projector_level_congruence j iota hsplit hmn τ) T x hx
  have hl : x ≫ σ.map (j.projector iota hsplit m τ) = x := hc.symm.trans hs
  refine ⟨AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift (q ^ m) (σ.map (j.projector iota hsplit m τ)) x hx hl, ?_⟩
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)))).mp
  rw [Category.assoc, nativeBlockEmbedding_inclusion, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion]

include hbound in
theorem native_high_kernel_from_low {H : Over S}
    (u : H ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) (σ.map (j.projector iota hsplit m τ)))
    (hu : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ)) ≫ f) u) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) ≫ f)
      (u ≫ nativeBlockEmbedding j iota hsplit A σ hmn τ) := by
  apply MixedKernelExhaustion.prescribedKernel_of_kernel_factors _ _ u
  · rw [← Category.assoc, nativeBlockEmbedding_inclusion]
    exact hu
  · exact native_kernel_factors_low j iota hsplit A σ hmn τ f hbound

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion
