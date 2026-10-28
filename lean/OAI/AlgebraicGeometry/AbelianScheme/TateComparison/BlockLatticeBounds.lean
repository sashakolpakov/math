import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockPreimages
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedBlockKernel

/-! # Block Lattice Bounds -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The multiplier bounds each actual chosen and opposite block
preimage by the original integral block. The witness is the constructed
polarization reverse map restricted to that block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

section

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N n : ℕ}
  {P Q : PEL.PELFamilyData R g N S}
  {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (q : ℕ) [Fact q.Prime] (e : PELIsogenies.PELIsogeny P Q n)
  (δ : Fin g → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (hq : Nat.Coprime q (∏ i, δ i))

theorem PELIsogenies.PELIsogeny.targetTatePreimage_multiplier
    (y : Add.schemeTateModule Q.abelian.scheme (Over.mk b) q) :
    (n : ℤ_[q]) • (PreimageQuotient.targetTatePreimageEquiv b q e.isogeny y).val =
      1 ⊗ₜ[ℤ_[q]] (e.integralTateReverse b q δ hδ hq y) := by
  have hy := congrArg (fun f => f y) (e.comp_integralTateReverse b q δ hδ hq)
  change Add.schemeTateMap P.abelian.scheme (Over.mk b) q e.isogeny.hom
    (e.integralTateReverse b q δ hδ hq y) = n • y at hy
  have he := PreimageQuotient.targetTatePreimageEquiv_map b q e.isogeny (e.integralTateReverse b q δ hδ hq y)
  rw [hy, map_nsmul] at he
  simpa only [Nat.cast_smul_eq_nsmul, Submodule.coe_smul_of_tower] using he

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {k : Type} [Field k] [IsAlgClosed k] {m : ℕ}
  {P Q : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m)) (δ : Fin (3 * s) → ℕ)
  (hδ : P.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

def Data.SphericalPELAlbaneseData.tateReverseBlockMap (v : Fin s × Bool) :
    D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v →ₗ[ℤ_[q]]
      D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) P v :=
  ProductActionDecomposition.ProductAction.blockMap (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) Q)
    (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) P)
    (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq)
    (D.tateReverse_splitAction_commute h e δ hδ hq) v

include δ hδ hq in
theorem Data.SphericalPELAlbaneseData.blockTatePreimage_bound (v : Fin s × Bool)
    (z : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
    (hz : z ∈ D.blockTatePreimage h (𝟙 (Spec (.of k))) e v) :
    (q : ℤ_[q]) ^ m • z ∈ D.integralBlockImage h (𝟙 (Spec (.of k))) P v := by
  obtain ⟨y, rfl⟩ := hz
  refine ⟨D.tateReverseBlockMap h e δ hδ hq v y, ?_⟩
  change 1 ⊗ₜ[ℤ_[q]] (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq y.val) =
    (q : ℤ_[q]) ^ m • (PreimageQuotient.targetTatePreimageEquiv (𝟙 (Spec (.of k))) q e.isogeny y.val).val
  rw [← Nat.cast_pow]
  exact (e.targetTatePreimage_multiplier (𝟙 (Spec (.of k))) q δ hδ hq y.val).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
