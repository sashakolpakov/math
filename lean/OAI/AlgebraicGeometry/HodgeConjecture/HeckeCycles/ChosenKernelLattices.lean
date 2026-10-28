import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedKernelDetection
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricLatticeTargets

/-! # Chosen Kernel Lattices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenKernelLattices.CM

noncomputable section

/-! Equal chosen kernels force equal chosen Tate lattices. The common
multiplier supplies a denominator bound through the original polarized
isogeny reverse map; no equality of lattices is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {k : Type} [Field k] [IsAlgClosed k] {m : ℕ}
  {P Q Q' : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k))}
  (e : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q (q ^ m)) (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q' (q ^ m))
  (frame : AbelianScheme.TateComparison.Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
  (hf : AbelianScheme.TateComparison.Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
  (δ : Fin (3 * s) → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (hq : Nat.Coprime q (∏ i, δ i))

theorem divided_reverse (v : Fin s × Bool)
    (y : D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) Q v) :
    AbelianScheme.TateComparison.ScaledKernel.Tate.dividedIntegralVector q m (D.tateReverseBlockMap hg e δ hδ hq v y).val =
      D.targetBlockToTateSpace hg (𝟙 (Spec (.of k))) e v y := by
  have h := e.targetTatePreimage_multiplier (𝟙 (Spec (.of k))) q δ hδ hq y.val
  rw [Nat.cast_pow] at h
  change (q ^ m : ℤ_[q]) • D.targetBlockToTateSpace hg (𝟙 (Spec (.of k))) e v y =
    1 ⊗ₜ[ℤ_[q]] (D.tateReverseBlockMap hg e δ hδ hq v y).val at h
  unfold AbelianScheme.TateComparison.ScaledKernel.Tate.dividedIntegralVector
  rw [← h]
  have hs : (q ^ m : ℤ_[q]) • D.targetBlockToTateSpace hg (𝟙 (Spec (.of k))) e v y =
      (q : ℚ_[q]) ^ m • D.targetBlockToTateSpace hg (𝟙 (Spec (.of k))) e v y := by
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [hs]
  exact inv_smul_smul₀ (pow_ne_zero m (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) _

include hf δ hδ hq in
theorem lattice_le_of_block_kernel (v : Fin s × Bool)
    (hker : ∀ z : D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) P v,
      (z.val.val m).val.toMul ≫ e.isogeny.hom = 1 →
        (z.val.val m).val.toMul ≫ f.isogeny.hom = 1) :
    AbelianScheme.TateComparison.Rational.framedTateLattice frame e.isogeny.hom v ≤ AbelianScheme.TateComparison.Rational.framedTateLattice frame f.isogeny.hom v := by
  intro z hz
  rw [← D.framedTargetBlockMap_range hg e frame hf δ hδ hq v] at hz
  obtain ⟨y, rfl⟩ := hz
  let x := D.tateReverseBlockMap hg e δ hδ hq v y
  have he : frame (AbelianScheme.TateComparison.ScaledKernel.Tate.dividedIntegralVector q m x.val) v =
      D.framedTargetBlockMap hg e frame v y := by
    rw [divided_reverse]
    rfl
  rw [← he]
  apply (D.framedBlock_mem_iff_kernel hg f frame hf δ hδ hq m v x).mpr
  apply hker
  apply (D.framedBlock_mem_iff_kernel hg e frame hf δ hδ hq m v x).mp
  rw [he, ← D.framedTargetBlockMap_range hg e frame hf δ hδ hq v]
  exact ⟨y, rfl⟩

include hf δ hδ hq in
theorem lattice_eq_of_block_kernel (v : Fin s × Bool)
    (hker : ∀ z : D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) P v,
      (z.val.val m).val.toMul ≫ e.isogeny.hom = 1 ↔
        (z.val.val m).val.toMul ≫ f.isogeny.hom = 1) :
    AbelianScheme.TateComparison.Rational.framedTateLattice frame e.isogeny.hom v = AbelianScheme.TateComparison.Rational.framedTateLattice frame f.isogeny.hom v :=
  le_antisymm (lattice_le_of_block_kernel D hg e f frame hf δ hδ hq v (fun z => (hker z).mp))
    (lattice_le_of_block_kernel D hg f e frame hf δ hδ hq v (fun z => (hker z).mpr))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenKernelLattices.CM
