import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusWeights
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FormMonomialBasis
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialCartierProjection

/-! # Form Frobenius Weights -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.FormFrobeniusWeights.PrimeFormFrobeniusWeights

noncomputable section

/-!
# Integral Frobenius weight maps in every polynomial form degree

Raising multiplies each exponent-plus-exterior weight by p. Lowering
divides the retained weights by p and kills the remaining basis vectors.
Their composites are the identity and the actual Cartier projection.
-/

open Classical

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W

def indicator {n : ℕ} (s : Set.powersetCard σ n) (i : σ) : ℕ := if i ∈ s then 1 else 0

theorem indicator_le {n : ℕ} (s : Set.powersetCard σ n) (i : σ) : indicator σ s i ≤ 1 := by
  unfold indicator
  split_ifs <;> omega

def retained {n : ℕ} (s : Set.powersetCard σ n) (d : σ →₀ ℕ) : Prop :=
  ∀ i, p ∣ d i + indicator σ s i

variable [Fintype σ]

def raiseExponent {n : ℕ} (s : Set.powersetCard σ n) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i =>
    PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raiseIndex p (indicator σ s i) (d i))

def lowerExponent {n : ℕ} (s : Set.powersetCard σ n) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i =>
    PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lowerIndex p (indicator σ s i) (d i))

theorem raise_retained {n : ℕ} (s : Set.powersetCard σ n) (d : σ →₀ ℕ) :
    retained p σ s (raiseExponent p σ s d) := by
  intro i
  exact PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raiseIndex_dvd p (indicator σ s i) (d i)

theorem lower_raiseExponent {n : ℕ} (s : Set.powersetCard σ n) (d : σ →₀ ℕ) :
    lowerExponent p σ s (raiseExponent p σ s d) = d := by
  ext i
  exact PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lower_raiseIndex p (indicator σ s i) (d i)

omit [Fact p.Prime] in
theorem raise_lowerExponent {n : ℕ} (s : Set.powersetCard σ n) (d : σ →₀ ℕ)
    (h : retained p σ s d) : raiseExponent p σ s (lowerExponent p σ s d) = d := by
  ext i
  exact PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise_lowerIndex p (indicator σ s i) (d i)
    (indicator_le σ s i) (h i)

variable [LinearOrder σ]

def raise (n : ℕ) : Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) :=
  (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n).constr W
    (fun ds => Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (raiseExponent p σ ds.2 ds.1, ds.2))

def lower (n : ℕ) : Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) :=
  (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n).constr W
    (fun ds => if retained p σ ds.2 ds.1 then
      Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (lowerExponent p σ ds.2 ds.1, ds.2) else 0)

theorem raise_basis (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    raise p k σ n (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s)) =
      Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (raiseExponent p σ s d, s) :=
  Module.Basis.constr_basis _ _ _ _

theorem lower_basis (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    lower p k σ n (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s)) =
      if retained p σ s d then
        Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (lowerExponent p σ s d, s) else 0 :=
  Module.Basis.constr_basis _ _ _ _

variable [CharP k p]

theorem projection_basis (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    (show Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) from
      ((PolynomialCartierProjection.PrimePolynomialCartierProjection.projection p k σ).f n).hom)
      (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s)) =
        if retained p σ s d then Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s) else 0 := by
  classical
  rw [Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis_apply]
  have h := PolynomialCartierProjection.PrimePolynomialCartierProjection.projection_word p k σ n d 1
    (Set.powersetCard.ofFinEmbEquiv.symm s)
  refine h.trans (ite_cond_congr ?_)
  apply propext
  simp only [retained, indicator, Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]

omit [CharP k p] in
theorem lower_raise (n : ℕ) : (lower p k σ n).comp (raise p k σ n) = LinearMap.id := by
  apply (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n).ext
  rintro ⟨d, s⟩
  simp only [LinearMap.comp_apply, LinearMap.id_apply, raise_basis, lower_basis,
    ite_eq_left (raise_retained p σ s d), lower_raiseExponent]

theorem raise_lower (n : ℕ) : (raise p k σ n).comp (lower p k σ n) =
    ((PolynomialCartierProjection.PrimePolynomialCartierProjection.projection p k σ).f n).hom := by
  apply (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n).ext
  rintro ⟨d, s⟩
  change raise p k σ n (lower p k σ n (Polynomial.FormMonomialBasis.PolynomialFormMonomialBasis.basis W σ n (d, s))) = _
  rw [lower_basis, projection_basis]
  by_cases h : retained p σ s d
  · rw [ite_eq_left h, raise_basis, raise_lowerExponent p σ s d h, ite_eq_left h]
  · rw [ite_eq_right h, map_zero, ite_eq_right h]

omit [CharP k p] in
theorem raise_injective (n : ℕ) : Function.Injective (raise p k σ n) :=
  Function.HasLeftInverse.injective ⟨lower p k σ n, fun x => LinearMap.congr_fun (lower_raise p k σ n) x⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.FormFrobeniusWeights.PrimeFormFrobeniusWeights
