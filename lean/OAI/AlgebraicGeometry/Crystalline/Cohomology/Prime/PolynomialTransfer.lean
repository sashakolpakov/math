import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DegreewiseTransferComp
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-! # Polynomial Transfer -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialTransfer.PrimePolynomialTransfer

noncomputable section

/-!
# An integral bounded transfer for polynomial Frobenius

With N coordinates, the transfer in degree n is p^(N-n) times weight
lowering. Both composites are p^N times the identity or the Cartier
projection. Injectivity of the actual Frobenius components assembles
the transfer into a chain map.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex W σ
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.map p k σ
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialCartierProjection.PrimePolynomialCartierProjection.projection p k σ

def degree (n : ℕ) : Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) :=
  (p : W) ^ (Fintype.card σ - n) • FormFrobeniusWeights.PrimeFormFrobeniusWeights.lower p k σ n

omit [CharP k p] in
theorem degree_comp_frobenius (n : ℕ) :
    (degree p k σ n).comp
      (show Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) from ((F).f n).hom) =
        (p : W) ^ Fintype.card σ • LinearMap.id := by
  rw [PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.map_f]
  apply (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n).ext
  rintro ⟨d, s⟩
  have hn : n ≤ Fintype.card σ := (show s.val.card = n from s.property) ▸ Finset.card_le_univ s.val
  change (p : W) ^ (Fintype.card σ - n) • FormFrobeniusWeights.PrimeFormFrobeniusWeights.lower p k σ n
      ((p : W) ^ n • FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise p k σ n
        (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s))) =
    (p : W) ^ Fintype.card σ • Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s)
  rw [map_smul, FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise_basis,
    FormFrobeniusWeights.PrimeFormFrobeniusWeights.lower_basis,
    ite_eq_left (FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise_retained p σ s d),
    FormFrobeniusWeights.PrimeFormFrobeniusWeights.lower_raiseExponent, smul_smul, ← pow_add, Nat.sub_add_cancel hn]

theorem frobenius_comp_degree (n : ℕ) :
    (show Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) from ((F).f n).hom).comp (degree p k σ n) =
      (p : W) ^ Fintype.card σ •
        (show Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) from ((C).f n).hom) := by
  rw [PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.map_f]
  apply (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n).ext
  rintro ⟨d, s⟩
  have hn : n ≤ Fintype.card σ := (show s.val.card = n from s.property) ▸ Finset.card_le_univ s.val
  change (p : W) ^ n • FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise p k σ n
      ((p : W) ^ (Fintype.card σ - n) • FormFrobeniusWeights.PrimeFormFrobeniusWeights.lower p k σ n
        (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s))) =
    (p : W) ^ Fintype.card σ • (show Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) from ((C).f n).hom)
      (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s))
  rw [map_smul, ← LinearMap.comp_apply, FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise_lower,
    smul_smul, ← pow_add, Nat.add_sub_of_le hn]

theorem frobenius_injective (n : ℕ) : Function.Injective ((F).f n) := by
  let : Module.IsTorsionFree W (Koszul.Tensor.KoszulTensor.Term W σ P n) :=
    (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n).isTorsionFree
  intro x y h
  apply FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise_injective p k σ n
  apply smul_right_injective (Koszul.Tensor.KoszulTensor.Term W σ P n) (pow_ne_zero n (WittVector.p_nonzero p k))
  change ((p : W) ^ n • FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise p k σ n) x =
    ((p : W) ^ n • FormFrobeniusWeights.PrimeFormFrobeniusWeights.raise p k σ n) y
  rw [← PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.map_f]
  exact h

instance frobenius_mono (n : ℕ) : Mono ((F).f n) :=
  (ModuleCat.mono_iff_injective ((F).f n)).mpr (frobenius_injective p k σ n)

def chain : K ⟶ K :=
  DegreewiseTransferComp.DegreewiseTransfer.chain W K F C (fun n => ModuleCat.ofHom (degree p k σ n))
    ((p : W) ^ Fintype.card σ) (fun n => frobenius_mono p k σ n)
    (fun n => ModuleCat.hom_ext (frobenius_comp_degree p k σ n))

theorem frobenius_chain : F ≫ chain p k σ = (p : W) ^ Fintype.card σ • 𝟙 K := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ModuleCat.hom_ext (degree_comp_frobenius p k σ n)

theorem chain_frobenius : chain p k σ ≫ F = (p : W) ^ Fintype.card σ • C :=
  DegreewiseTransferComp.DegreewiseTransfer.chain_comp W K F C (fun n => ModuleCat.ofHom (degree p k σ n))
    ((p : W) ^ Fintype.card σ) (fun n => frobenius_mono p k σ n)
    (fun n => ModuleCat.hom_ext (frobenius_comp_degree p k σ n))

def homotopy : Homotopy ((p : W) ^ Fintype.card σ • 𝟙 K) (chain p k σ ≫ F) := by
  rw [chain_frobenius]
  exact (PolynomialCartierProjection.PrimePolynomialCartierProjection.homotopy p k σ).smul ((p : W) ^ Fintype.card σ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialTransfer.PrimePolynomialTransfer
