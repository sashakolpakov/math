import OAI.AlgebraicGeometry.ComplexMultiplication.DecompositionEmbeddingBasis
import OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorTypedBasis
import OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorBalance

/-! # Exterior Hodge Type -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorHodgeType.CM

noncomputable section

/-!
# The induced exterior Hodge types

The exterior types are defined from the given holomorphic and
antiholomorphic subspaces, by taking spans of wedges of pure vectors and
using the canonical coefficient comparison. They do not depend on a CM
basis. The CM basis is then proved to diagonalize these subspaces, so the
rational orbitwise balance theorem applies to the intrinsic `(p,p)` type.
The comparison with higher geometric cohomology is still a separate step.
-/

open scoped TensorProduct Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

namespace WeightOneHodgeStructure

/-- Signed exterior type, induced from the two given degree-one Hodge subspaces. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.exteriorSignedSubspace (H : WeightOne.CM.WeightOneHodgeStructure U) (n : ℕ) (w : ℤ) :
    Submodule ℂ (WeightOne.CM.Complexification (⋀[ℚ]^n U)) :=
  (ExteriorTypedBasis.CM.exteriorSignedSpan H.signSubspace n w).map (ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ U n).symm.toLinearMap

/-- The induced `(p,q)` Hodge type on the complexification of the rational exterior power.
The signed-degree condition is equivalent to exactly `p` holomorphic and `q`
antiholomorphic factors, by `signTotal_eq_sub_iff_counts`. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.exteriorPureSubspace (H : WeightOne.CM.WeightOneHodgeStructure U) (p q : ℕ) :
    Submodule ℂ (WeightOne.CM.Complexification (⋀[ℚ]^(p + q) U)) :=
  H.exteriorSignedSubspace (p + q) ((p : ℤ) - q)

/-- Wedges of `p` holomorphic and `q` antiholomorphic vectors have induced type `(p,q)`. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.exteriorPureSubspace_contains_wedge (H : WeightOne.CM.WeightOneHodgeStructure U) (p q : ℕ)
    (ε : Fin (p + q) → Bool) (v : Fin (p + q) → WeightOne.CM.Complexification U)
    (hp : Fintype.card {i // ε i = true} = p) (hq : Fintype.card {i // ε i = false} = q)
    (hv : ∀ i, v i ∈ H.signSubspace (ε i)) :
    (ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ U (p + q)).symm (exteriorPower.ιMulti ℂ (p + q) v) ∈
      H.exteriorPureSubspace p q := by
  apply Submodule.mem_map.mpr
  refine ⟨exteriorPower.ιMulti ℂ (p + q) v, ?_, rfl⟩
  exact Submodule.subset_span ⟨ε, v, (ExteriorTypedBasis.CM.signTotal_eq_sub_iff_counts p q ε).mpr ⟨hp, hq⟩, hv, rfl⟩

end WeightOneHodgeStructure

namespace CMDecomposition

variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H) (n : ℕ)

local instance : LinearOrder D.EmbeddingIndex := linearOrderOfSTO WellOrderingRel

/-- The intrinsic exterior Hodge type is diagonal in the actual CM embedding basis. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorSignedSubspace_eq_span (w : ℤ) :
    H.exteriorSignedSubspace n w = Submodule.span ℂ
      ((D.complexExteriorEmbeddingBasis n) '' {t | D.exteriorSignSum n t 1 = w}) := by
  unfold WeightOne.CM.WeightOneHodgeStructure.exteriorSignedSubspace
  rw [ExteriorTypedBasis.CM.exteriorSignedSpan_eq_basisSpan n D.embeddingBasis D.embeddingSign w H.signSubspace
    D.signSubspace_eq_span_embeddingBasis]
  unfold ExteriorTypedBasis.CM.exteriorSignedBasisSpan
  rw [Submodule.map_span, Set.image_image]
  have hw : {t | ExteriorTypedBasis.CM.exteriorBasisSignSum n D.embeddingSign t = w} =
      {t | D.exteriorSignSum n t 1 = w} := by
    ext t
    simp only [ExteriorTypedBasis.CM.exteriorBasisSignSum, Decomposition.CM.CMDecomposition.exteriorSignSum, Decomposition.CM.CMDecomposition.galoisSign_one]
  rw [hw]
  apply congrArg (Submodule.span ℂ)
  apply congrArg (fun f : D.ExteriorIndex n → WeightOne.CM.Complexification (⋀[ℚ]^n U) =>
    f '' {t | D.exteriorSignSum n t 1 = w})
  funext t
  unfold Decomposition.CM.CMDecomposition.complexExteriorEmbeddingBasis
  simp only [Module.Basis.map_apply, LinearEquiv.coe_coe]

/-- Induced `(p,p)` exterior Hodge type is exactly the diagonal balanced subspace. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorPureSubspace_self_eq_balanced (p : ℕ) :
    H.exteriorPureSubspace p p = D.balancedExteriorSubspace (p + p) := by
  unfold WeightOne.CM.WeightOneHodgeStructure.exteriorPureSubspace
  rw [sub_self, D.exteriorSignedSubspace_eq_span]
  rfl

/-- Rational vectors of intrinsic exterior Hodge type `(p,p)` use only orbitwise balanced monomials. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.rational_exterior_hodge_mem_orbitBalanced (p : ℕ) (u : ⋀[ℚ]^(p + p) U)
    (hu : (1 : ℂ) ⊗ₜ[ℚ] u ∈ H.exteriorPureSubspace p p) :
    (1 : ℂ) ⊗ₜ[ℚ] u ∈ D.orbitBalancedExteriorSubspace (p + p) := by
  rw [D.exteriorPureSubspace_self_eq_balanced] at hu
  exact D.rational_balanced_mem_orbitBalanced (p + p) u hu

end CMDecomposition

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorHodgeType.CM
