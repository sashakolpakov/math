import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Bilinear Coordinates -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.BilinearCoordinates

/-! Coordinate bilinear forms and uniqueness of their complex extension
from all real vectors. -/

open scoped Classical

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.DataTheta

def crossForm (R I : Type*) [CommRing R] [Fintype I] :
    ((I → R) × (I → R)) →ₗ[R] ((I → R) × (I → R)) →ₗ[R] R :=
  (dotProductBilin R R).compl₁₂ (LinearMap.fst R _ _) (LinearMap.snd R _ _) -
    (dotProductBilin R R).compl₁₂ (LinearMap.snd R _ _) (LinearMap.fst R _ _)

def standardForm (R I : Type*) [CommRing R] [Fintype I] :
    ((I ⊕ I) → R) →ₗ[R] ((I ⊕ I) → R) →ₗ[R] R :=
  (crossForm R I).compl₁₂
    (LinearEquiv.sumArrowLequivProdArrow I I R R).toLinearMap
    (LinearEquiv.sumArrowLequivProdArrow I I R R).toLinearMap

theorem standardForm_apply {R I : Type} [CommRing R] [Fintype I]
    (x y : (I ⊕ I) → R) : standardForm R I x y = DataTheta.standardPairing x y := by
  change (∑ i, x (.inl i) * y (.inr i)) - (∑ i, x (.inr i) * y (.inl i)) = _
  rw [DataTheta.standardPairing, Finset.sum_sub_distrib]

theorem complex_basis_real {I : Type*} [Fintype I] (i : I) :
    (Pi.basisFun ℂ I) i = fun j => (((Pi.basisFun ℝ I) i j) : ℂ) := by
  funext j
  simp only [Pi.basisFun_apply, Pi.single_apply]
  split_ifs <;> norm_num

theorem complexBilinear_ext_real {I : Type*} [Fintype I]
    (f g : (I → ℂ) →ₗ[ℂ] (I → ℂ) →ₗ[ℂ] ℂ)
    (hr : ∀ x y : I → ℝ, f (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) =
      g (fun i => (x i : ℂ)) (fun i => (y i : ℂ))) : f = g := by
  apply (Pi.basisFun ℂ I).ext
  intro i
  apply (Pi.basisFun ℂ I).ext
  intro j
  rw [complex_basis_real, complex_basis_real]
  exact hr _ _

end RepresentationTheory.Theta.Adelic.BilinearCoordinates

namespace RepresentationTheory.Theta.Adelic.BilinearCoordinates.Symplectic

/-! Actual symplectic matrices from coordinate pairing preservation,
with the explicit Schrödinger-to-Siegel phase swap. -/

open scoped Classical

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.DataTheta
variable {I k : Type} [Fintype I] [DecidableEq I] [Field k]

theorem standardPairing_eq_negJ (x y : (I ⊕ I) → k) :
    DataTheta.standardPairing x y = -(Matrix.J I k).toBilin' x y := by
  simp [DataTheta.standardPairing, Matrix.toBilin'_apply, Matrix.J, Fintype.sum_sum_type,
    Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib]
  ring

theorem matrix_symplectic_of_preserves (M : Matrix (I ⊕ I) (I ⊕ I) k)
    (hp : ∀ x y, DataTheta.standardPairing (M.mulVec x) (M.mulVec y) = DataTheta.standardPairing x y) :
    M ∈ Matrix.symplecticGroup I k := by
  apply SymplecticGroup.mem_iff'.mpr
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (Matrix.J I k).toBilin' (M.mulVec x) (M.mulVec y) = (Matrix.J I k).toBilin' x y
  have h := congrArg Neg.neg (hp x y)
  simpa only [standardPairing_eq_negJ, neg_neg] using h

theorem symplectic_preserves_standard (g : Matrix.symplecticGroup I k)
    (x y : (I ⊕ I) → k) :
    DataTheta.standardPairing (g.val.mulVec x) (g.val.mulVec y) = DataTheta.standardPairing x y := by
  have h := congrArg Matrix.toBilin' (SymplecticGroup.mem_iff'.mp g.property)
  rw [← Matrix.toBilin'_comp] at h
  have he := congrArg (fun B : LinearMap.BilinForm k ((I ⊕ I) → k) => B x y) h
  rw [standardPairing_eq_negJ, standardPairing_eq_negJ]
  exact congrArg Neg.neg he

def linearSymplectic (e : ((I ⊕ I) → k) ≃ₗ[k] ((I ⊕ I) → k))
    (hp : ∀ x y, DataTheta.standardPairing (e x) (e y) = DataTheta.standardPairing x y) :
    Matrix.symplecticGroup I k :=
  ⟨LinearMap.toMatrix' e.toLinearMap, matrix_symplectic_of_preserves _ (by
    intro x y
    simpa only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] using hp x y)⟩

theorem linearSymplectic_action (e : ((I ⊕ I) → k) ≃ₗ[k] ((I ⊕ I) → k))
    (hp : ∀ x y, DataTheta.standardPairing (e x) (e y) = DataTheta.standardPairing x y) (x : (I ⊕ I) → k) :
    (linearSymplectic e hp).val.mulVec x = e x := LinearMap.toMatrix'_mulVec e.toLinearMap x

theorem linearSymplectic_entry (e : ((I ⊕ I) → k) ≃ₗ[k] ((I ⊕ I) → k))
    (hp : ∀ x y, DataTheta.standardPairing (e x) (e y) = DataTheta.standardPairing x y) (i j : I ⊕ I) :
    (linearSymplectic e hp).val i j = e (Pi.single j 1) i := rfl

def phaseSwapLinear : ((I ⊕ I) → k) ≃ₗ[k] ((I ⊕ I) → k) where
  toFun := DataTheta.swapPhase
  invFun := DataTheta.swapPhase
  left_inv x := by funext i; cases i <;> rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' c x := by funext i; cases i <;> rfl

omit [DecidableEq I] in
theorem phaseSwap_pairing (x y : (I ⊕ I) → k) :
    DataTheta.standardPairing (phaseSwapLinear x) (phaseSwapLinear y) = -DataTheta.standardPairing x y := by
  change (∑ i, (x (.inr i) * y (.inl i) - x (.inl i) * y (.inr i))) =
    -(∑ i, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i)))
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

def swapConjugate (e : ((I ⊕ I) → k) ≃ₗ[k] ((I ⊕ I) → k)) :
    ((I ⊕ I) → k) ≃ₗ[k] ((I ⊕ I) → k) :=
  phaseSwapLinear.symm.trans (e.trans phaseSwapLinear)

omit [Fintype I] [DecidableEq I] in
theorem swapConjugate_apply (e : ((I ⊕ I) → k) ≃ₗ[k] ((I ⊕ I) → k))
    (x : (I ⊕ I) → k) : swapConjugate e x = DataTheta.swapPhase (e (DataTheta.swapPhase x)) := rfl

omit [DecidableEq I] in
theorem swapConjugate_preserves (e : ((I ⊕ I) → k) ≃ₗ[k] ((I ⊕ I) → k))
    (hp : ∀ x y, DataTheta.standardPairing (e x) (e y) = DataTheta.standardPairing x y)
    (x y : (I ⊕ I) → k) :
    DataTheta.standardPairing (swapConjugate e x) (swapConjugate e y) = DataTheta.standardPairing x y := by
  change DataTheta.standardPairing (phaseSwapLinear (e (phaseSwapLinear x)))
    (phaseSwapLinear (e (phaseSwapLinear y))) = _
  rw [phaseSwap_pairing, hp, phaseSwap_pairing, neg_neg]

theorem blocks_matrix (g : Matrix.symplecticGroup I k) :
    DataTheta.blockMatrix (PoissonAutomorphyNormalizationData.blocks g) = g.val := Matrix.fromBlocks_toBlocks g.val

theorem linearSymplectic_rat_real
    (f : ((I ⊕ I) → ℝ) ≃ₗ[ℝ] ((I ⊕ I) → ℝ))
    (g : ((I ⊕ I) → ℚ) ≃ₗ[ℚ] ((I ⊕ I) → ℚ))
    (hf : ∀ x y, DataTheta.standardPairing (f x) (f y) = DataTheta.standardPairing x y)
    (hg : ∀ x y, DataTheta.standardPairing (g x) (g y) = DataTheta.standardPairing x y)
    (hc : ∀ x : (I ⊕ I) → ℚ, f (fun i => (x i : ℝ)) = fun i => (g x i : ℝ)) :
    (linearSymplectic f hf).val = (linearSymplectic g hg).val.map (algebraMap ℚ ℝ) := by
  apply Matrix.ext
  intro i j
  rw [linearSymplectic_entry, Matrix.map_apply, linearSymplectic_entry]
  change f (Pi.single j 1) i = (g (Pi.single j 1) i : ℝ)
  have hs : (Pi.single j (1 : ℝ) : (I ⊕ I) → ℝ) =
      fun i => (((Pi.single j (1 : ℚ) : (I ⊕ I) → ℚ) i) : ℝ) := by
    funext k
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [hs]
  exact congrFun (hc (Pi.single j 1)) i

end RepresentationTheory.Theta.Adelic.BilinearCoordinates.Symplectic

end

end OAI
