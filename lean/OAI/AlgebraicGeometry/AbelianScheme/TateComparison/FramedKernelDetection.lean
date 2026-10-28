import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedPreimageDecomposition
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScaledKernel

/-! # Framed Kernel Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! A chosen projected lattice detects the actual finite-level kernel
on that block. The proof uses the support of divided integral vectors
and the product decomposition of the full isogeny preimage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {k : Type} [Field k] [IsAlgClosed k] {m : ℕ}
  {P Q : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m))
  (frame : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
  (hf : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
  (δ : Fin (3 * s) → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (hq : Nat.Coprime q (∏ i, δ i))

include hg hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.preimage_mem_iff_framed_of_single (v : Fin s × Bool)
    (z : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
    (hsingle : frame z = Pi.single v (frame z v)) :
    z ∈ Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom ↔
      frame z v ∈ Rational.framedTateLattice frame e.isogeny.hom v := by
  constructor
  · intro hz
    exact ⟨frame z, ⟨z, hz, rfl⟩, rfl⟩
  · intro hz
    obtain ⟨w, hw, he⟩ := D.framedTateLattice_single_mem hg e frame hf δ hδ hq v (frame z v) hz
    have hwz : w = z := frame.injective (he.trans hsingle.symm)
    exact hwz ▸ hw

include hg hf in
omit [IsAlgClosed k] in
theorem Data.SphericalPELAlbaneseData.dividedIntegralBlock_frame_single (r : ℕ) (v : Fin s × Bool)
    (z : D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) P v) :
    frame (ScaledKernel.Tate.dividedIntegralVector q r z.val) =
      Pi.single v (frame (ScaledKernel.Tate.dividedIntegralVector q r z.val) v) := by
  classical
  funext w i
  by_cases hw : w = v
  · subst w
    simp only [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hw]
    change frame (((q : ℚ_[q]) ^ r)⁻¹ • (1 ⊗ₜ[ℤ_[q]] z.val)) w i = 0
    rw [map_smul]
    change ((q : ℚ_[q]) ^ r)⁻¹ * frame (1 ⊗ₜ[ℤ_[q]] z.val) w i = 0
    rw [D.integralFrameCoordinate_off_block hg _ P frame hf (Ne.symm hw) z i, mul_zero]

include hg hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.framedBlock_mem_iff_kernel (r : ℕ) (v : Fin s × Bool)
    (z : D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) P v) :
    frame (ScaledKernel.Tate.dividedIntegralVector q r z.val) v ∈ Rational.framedTateLattice frame e.isogeny.hom v ↔
      (z.val.val r).val.toMul ≫ e.isogeny.hom = 1 :=
  (D.preimage_mem_iff_framed_of_single hg e frame hf δ hδ hq v _
    (D.dividedIntegralBlock_frame_single hg frame hf r v z)).symm.trans
      (ScaledKernel.dividedIntegralVector_mem_preimage_iff _ q e.isogeny.hom r z.val)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
