import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PreimageQuotient
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockMaps

/-! # Block Preimages -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockPreimages.SphericalPELAlbaneseData

noncomputable section

/-! Chosen and opposite target blocks are pulled into the source rational
Tate space using the actual rational isogeny inverse. The resulting image
contains the original source block, and its quotient is the actual integral
Tate block cokernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {S : Scheme} {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ S)
  {P Q : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S}
  {n : ℕ} (e : PELIsogenies.PELIsogeny P Q n)

local instance : Module ℤ_[q] (Rational.rationalTateModule P.abelian.scheme (Over.mk b) q) :=
  TensorProduct.leftModule

local instance : Module ℚ_[q] (Rational.rationalTateModule P.abelian.scheme (Over.mk b) q) :=
  TensorProduct.leftModule

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.integralBlockEmbedding
    (P : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) (v : Fin s × Bool) :
    D.integralTateBlock h (Over.mk b) P v →ₗ[ℤ_[q]] Rational.rationalTateModule P.abelian.scheme (Over.mk b) q :=
  (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.schemeTateModule P.abelian.scheme (Over.mk b) q) 1).comp
    (D.integralTateBlock h (Over.mk b) P v).subtype

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.targetBlockToTateSpace (v : Fin s × Bool) :
    D.integralTateBlock h (Over.mk b) Q v →ₗ[ℤ_[q]] Rational.rationalTateModule P.abelian.scheme (Over.mk b) q :=
  (Rational.isogenyTatePreimage (T := Over.mk b) (q := q) e.isogeny.hom).subtype.comp
    ((PreimageQuotient.targetTatePreimageEquiv b q e.isogeny).toLinearMap.comp
      (D.integralTateBlock h (Over.mk b) Q v).subtype)

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.targetBlockToTateSpace_injective (v : Fin s × Bool) :
    Function.Injective (D.targetBlockToTateSpace h b e v) := by
  intro x y hxy
  apply Subtype.ext
  apply (PreimageQuotient.targetTatePreimageEquiv b q e.isogeny).injective
  exact Subtype.ext hxy

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.targetBlockToTateSpace_map (v : Fin s × Bool) :
    (D.targetBlockToTateSpace h b e v).comp (D.tateBlockMap h (Over.mk b) e v) =
      D.integralBlockEmbedding h b P v := by
  apply LinearMap.ext
  intro x
  exact PreimageQuotient.targetTatePreimageEquiv_map b q e.isogeny x.val

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.blockTatePreimage (v : Fin s × Bool) :
    Submodule ℤ_[q] (Rational.rationalTateModule P.abelian.scheme (Over.mk b) q) :=
  (D.targetBlockToTateSpace h b e v).range

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.integralBlockImage
    (P : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) (v : Fin s × Bool) :
    Submodule ℤ_[q] (Rational.rationalTateModule P.abelian.scheme (Over.mk b) q) :=
  (D.integralBlockEmbedding h b P v).range

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.integralBlockImage_le_preimage (v : Fin s × Bool) :
    D.integralBlockImage h b P v ≤ D.blockTatePreimage h b e v := by
  rintro z ⟨x, rfl⟩
  refine ⟨D.tateBlockMap h (Over.mk b) e v x, ?_⟩
  exact congrArg (fun f => f x) (D.targetBlockToTateSpace_map h b e v)

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.blockTatePreimage_le (v : Fin s × Bool) :
    D.blockTatePreimage h b e v ≤ Rational.isogenyTatePreimage (T := Over.mk b) (q := q) e.isogeny.hom := by
  rintro z ⟨x, rfl⟩
  exact (PreimageQuotient.targetTatePreimageEquiv b q e.isogeny x.val).property

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.sourceInBlockTatePreimage (v : Fin s × Bool) :
    Submodule ℤ_[q] (D.blockTatePreimage h b e v) :=
  (D.integralBlockImage h b P v).comap (D.blockTatePreimage h b e v).subtype

local instance (v : Fin s × Bool) : Module ℤ_[q] (D.blockTatePreimage h b e v) :=
  (D.blockTatePreimage h b e v).module

local instance (v : Fin s × Bool) : HasQuotient
    (D.blockTatePreimage h b e v) (Submodule ℤ_[q] (D.blockTatePreimage h b e v)) :=
  Submodule.hasQuotient (R := ℤ_[q]) (M := D.blockTatePreimage h b e v)

abbrev _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.blockTateLatticeQuotient (v : Fin s × Bool) :=
  D.blockTatePreimage h b e v ⧸ D.sourceInBlockTatePreimage h b e v

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.targetBlockPreimageEquiv (v : Fin s × Bool) :
    D.integralTateBlock h (Over.mk b) Q v ≃ₗ[ℤ_[q]] D.blockTatePreimage h b e v :=
  LinearEquiv.ofInjective (D.targetBlockToTateSpace h b e v)
    (D.targetBlockToTateSpace_injective h b e v)

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.targetBlockPreimageEquiv_range (v : Fin s × Bool) :
    (D.tateBlockMap h (Over.mk b) e v).range.map (D.targetBlockPreimageEquiv h b e v).toLinearMap =
      D.sourceInBlockTatePreimage h b e v := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (congrArg (fun f => f x) (D.targetBlockToTateSpace_map h b e v)).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨D.tateBlockMap h (Over.mk b) e v x, ⟨x, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun f => f x) (D.targetBlockToTateSpace_map h b e v)).trans hx

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.tateBlockCokernelEquivLatticeQuotient (v : Fin s × Bool) :
    (D.integralTateBlock h (Over.mk b) Q v ⧸ (D.tateBlockMap h (Over.mk b) e v).range) ≃ₗ[ℤ_[q]]
      (D.blockTatePreimage h b e v ⧸ D.sourceInBlockTatePreimage h b e v) :=
  Submodule.Quotient.equiv _ _ (D.targetBlockPreimageEquiv h b e v)
    (D.targetBlockPreimageEquiv_range h b e v)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockPreimages.SphericalPELAlbaneseData
