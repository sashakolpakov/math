import OAI.AlgebraicGeometry.ComplexMultiplication.OddSignSwitch
import OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorHodgeType

/-! # Exterior Sign Reduction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorSignReduction.CM

noncomputable section

/-!
# The odd sign-switch reduction for actual rational exterior Hodge vectors

The conjugation pairing is the intrinsic complex conjugation on the actual
common Galois CM field. Each monomial in the support of a rational exterior
Hodge vector supplies a balanced tuple of odd types on this group. Splitting
the tuple into identity and conjugate slots gives endpoints of a finite
chain of four-factor identities, every intermediate type being odd.
Algebraic realization of the types and of the switches remains necessary.
-/

open scoped TensorProduct Classical

namespace CMCoefficientField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

/-- Multiplication by CM conjugation pairs the scalar Galois automorphisms. -/
theorem conjugation_mul_involutive :
    Function.Involutive (fun g : Gal(K/ℚ) => GaloisSigns.CM.CMCoefficientField.conjugation K * g) := by
  intro g
  apply AlgEquiv.ext
  intro x
  exact GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply K (g x)

/-- No scalar Galois automorphism is fixed by that pairing. -/
theorem conjugation_mul_ne (g : Gal(K/ℚ)) : GaloisSigns.CM.CMCoefficientField.conjugation K * g ≠ g := by
  intro h
  apply GaloisSigns.CM.CMCoefficientField.conjugation_ne_one K
  exact mul_right_cancel (h.trans (one_mul g).symm)

end CMCoefficientField

namespace CMDecomposition

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H)

/-- An actual embedding line's Hodge signs, with their proved CM oddness. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.galoisOddSign (j : D.EmbeddingIndex) :
    OddSignSwitch.CM.OddSignPattern (fun g : Gal(D.commonCoefficientField/ℚ) =>
      GaloisSigns.CM.CMCoefficientField.conjugation D.commonCoefficientField * g) :=
  ⟨D.galoisSign j, D.galoisSign_conjugation_mul j⟩

local instance : LinearOrder D.EmbeddingIndex := linearOrderOfSTO WellOrderingRel

/-- Enumerate an exterior monomial by its distinct degree-one embedding indices. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorEmbeddingTuple (n : ℕ) (s : D.ExteriorIndex n) : Fin n → D.EmbeddingIndex :=
  Set.powersetCard.ofFinEmbEquiv.symm s

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exteriorEmbeddingTuple_signSum (n : ℕ) (s : D.ExteriorIndex n)
    (g : Gal(D.commonCoefficientField/ℚ)) :
    (∑ i, SignSwitch.CM.signValue (D.galoisSign (D.exteriorEmbeddingTuple n s i) g)) =
      D.exteriorSignSum n s g :=
  ExteriorTypedBasis.CM.sum_orderedExteriorIndex n (fun j => SignSwitch.CM.signValue (D.galoisSign j g)) s

/-- Every orbitwise balanced monomial has a finite reduction through odd CM types. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.exterior_balanced_oddSwitchChain (p : ℕ) (s : D.ExteriorIndex (p + p))
    (hs : ∀ g, D.exteriorSignSum (p + p) s g = 0) :
    OddSignSwitch.CM.OddSwitchChain
      (fun i : Fin p => D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s (Fin.castAdd p i)))
      (fun i : Fin p =>
        (D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s (Fin.natAdd p i))).neg) := by
  let : LinearOrder Gal(D.commonCoefficientField/ℚ) := linearOrderOfSTO WellOrderingRel
  let : Fintype Gal(D.commonCoefficientField/ℚ) := Fintype.ofFinite _
  apply OddSignSwitch.CM.balancedOddTuple_switchChain
    (fun g : Gal(D.commonCoefficientField/ℚ) =>
      GaloisSigns.CM.CMCoefficientField.conjugation D.commonCoefficientField * g)
    (CMCoefficientField.conjugation_mul_involutive D.commonCoefficientField)
    (CMCoefficientField.conjugation_mul_ne D.commonCoefficientField) p
    (fun i => D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s i))
  intro g
  exact (D.exteriorEmbeddingTuple_signSum (p + p) s g).trans (hs g)

/-- Apply the full odd sign reduction to every nonzero monomial coefficient of
a rational vector of intrinsic exterior Hodge type `(p,p)`. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition.rational_exterior_hodge_oddSwitchChain (p : ℕ) (u : ⋀[ℚ]^(p + p) U)
    (hu : (1 : ℂ) ⊗ₜ[ℚ] u ∈ H.exteriorPureSubspace p p)
    (s : D.ExteriorIndex (p + p))
    (hs : (D.exteriorEmbeddingBasis (p + p)).repr
      ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) s ≠ 0) :
    OddSignSwitch.CM.OddSwitchChain
      (fun i : Fin p => D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s (Fin.castAdd p i)))
      (fun i : Fin p =>
        (D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s (Fin.natAdd p i))).neg) := by
  apply D.exterior_balanced_oddSwitchChain p s
  rw [D.exteriorPureSubspace_self_eq_balanced] at hu
  exact D.rational_exterior_support_balanced (p + p) u hu s hs

end CMDecomposition

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorSignReduction.CM
