import OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationSpectralDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingSymmetricWeights
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingNilpotence

/-! # Derivation Nilpotence -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationNilpotence.Construction

noncomputable section

section

/-! Positive commutator eigenspaces strictly raise the eigenvalues of
the symmetric operator. Every positive bracket derivation is nilpotent. -/

open scoped Classical
open _root_.ContinuousLinearMap _root_.Module.End

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [Fintype ι]

def weightRaisingOperators (b : OrthonormalBasis ι ℝ L) (w : ι → ℝ) : Submodule ℝ (L →L[ℝ] L) where
  carrier := {X | ∀ i j, w i ≤ w j → b.repr (X (b j)) i = 0}
  zero_mem' := by intro i j _; simp
  add_mem' hX hY := by
    intro i j hij
    simp only [add_apply, map_add, PiLp.add_apply, hX i j hij, hY i j hij, add_zero]
  smul_mem' c _ hX := by
    intro i j hij
    simp only [smul_apply, map_smul, PiLp.smul_apply, hX i j hij, smul_zero]

omit [FiniteDimensional ℝ L] in
theorem positive_commutator_eigenvector_raises_weights
    (b : OrthonormalBasis ι ℝ L) (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : ι → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (X : L →L[ℝ] L) {r : ℝ} (hr : 0 < r) (hX : H * X - X * H = r • X) :
    X ∈ weightRaisingOperators b w := by
  intro i j hij
  have he := congrArg (fun T : L →L[ℝ] L => b.repr (T (b j)) i) hX
  simp only [sub_apply, mul_apply_eq_comp, smul_apply, map_sub, PiLp.sub_apply] at he
  rw [CommutingSymmetricWeights.Construction.orthonormal_eigen_coordinate b H hH w heig, heig] at he
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at he
  have hc : w i - w j - r ≠ 0 := by linarith
  apply (mul_eq_zero.mp (show (w i - w j - r) * b.repr (X (b j)) i = 0 by nlinarith)).resolve_left hc

theorem positiveBracketDerivations_le_weightRaising
    (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis ι ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : ι → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H ≤ weightRaisingOperators b w := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr X hX
  exact positive_commutator_eigenvector_raises_weights b H hH w heig X hr (mem_eigenspace_iff.mp hX.2)

omit [FiniteDimensional ℝ L] in
theorem weightRaisingOperators_isNilpotent {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (X : L →L[ℝ] L) (hX : X ∈ weightRaisingOperators b w) : IsNilpotent X := by
  have hm : IsNilpotent (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X) :=
    Weight.RaisingNilpotence.Construction.strictly_weight_raising_matrix_isNilpotent (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X) w (by
      intro i j hij
      change LinearMap.toMatrix b.toBasis b.toBasis X.toLinearMap i j = 0
      simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis] using! hX i j hij)
  have hinj : Function.Injective (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis) := by
    intro A C h
    have he := (LinearMap.toMatrix b.toBasis b.toBasis).injective h
    ext x
    exact DFunLike.congr_fun he x
  exact (IsNilpotent.map_iff hinj).mp hm

theorem positiveBracketDerivations_isNilpotent
    (B : L →L[ℝ] L →L[ℝ] L) (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (X : L →L[ℝ] L) (hX : X ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H) : IsNilpotent X := by
  let b := hH.eigenvectorBasis rfl
  let w := hH.eigenvalues rfl
  have heig (i : Fin (Module.finrank ℝ L)) : H (b i) = w i • b i :=
    hH.apply_eigenvectorBasis rfl i
  exact weightRaisingOperators_isNilpotent b w X (positiveBracketDerivations_le_weightRaising B b H hH w heig hX)

end

/-! Positive derivations are exactly the derivations strictly raising
the weights of the chosen symmetric operator. -/

open scoped Classical
open _root_.ContinuousLinearMap _root_.Module.End

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [Fintype ι]

omit [FiniteDimensional ℝ L] in
theorem commutator_eigen_coordinate
    (b : OrthonormalBasis ι ℝ L) (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : ι → ℝ) (heig : ∀ i, H (b i) = w i • b i) (X : L →L[ℝ] L) (i j : ι) :
    b.repr ((H * X - X * H) (b j)) i = (w i - w j) * b.repr (X (b j)) i := by
  simp only [sub_apply, mul_apply_eq_comp, map_sub, PiLp.sub_apply]
  rw [CommutingSymmetricWeights.Construction.orthonormal_eigen_coordinate b H hH w heig, heig]
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ L] in
theorem weightRaising_commutator_mem
    (b : OrthonormalBasis ι ℝ L) (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : ι → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (X : L →L[ℝ] L) (hX : X ∈ weightRaisingOperators b w) :
    H * X - X * H ∈ weightRaisingOperators b w := by
  intro i j hij
  rw [commutator_eigen_coordinate b H hH w heig, hX i j hij, mul_zero]

omit [FiniteDimensional ℝ L] in
theorem weightRaising_nonpositive_eigenvector_zero
    (b : OrthonormalBasis ι ℝ L) (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : ι → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (X : L →L[ℝ] L) (hX : X ∈ weightRaisingOperators b w)
    {r : ℝ} (hr : r ≤ 0) (hXe : H * X - X * H = r • X) : X = 0 := by
  have hzero (j : ι) : X (b j) = 0 := by
    apply b.repr.injective
    ext i
    change b.repr (X (b j)) i = b.repr 0 i
    rw [map_zero, PiLp.zero_apply]
    by_cases hij : w i ≤ w j
    · exact hX i j hij
    have he := congrArg (fun T : L →L[ℝ] L => b.repr (T (b j)) i) hXe
    rw [commutator_eigen_coordinate b H hH w heig] at he
    simp only [smul_apply, map_smul, PiLp.smul_apply, smul_eq_mul] at he
    have hc : w i - w j - r ≠ 0 := by linarith
    exact (mul_eq_zero.mp (show (w i - w j - r) * b.repr (X (b j)) i = 0 by nlinarith)).resolve_left hc
  have he : X.toLinearMap = 0 := b.toBasis.ext hzero
  ext x
  exact DFunLike.congr_fun he x

theorem positiveBracketDerivations_eq_weightRaising
    (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis ι ℝ L)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (w : ι → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H = DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B ⊓ weightRaisingOperators b w := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  apply le_antisymm
  · exact le_inf (InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule_le _ _)
      (positiveBracketDerivations_le_weightRaising B b H hH.1 w heig)
  · have hspan := DerivationSpectralDecomposition.Construction.selfAdjoint_commutator_invariant_eigenspace_span H hH.1
      (DerivationSpectralDecomposition.Construction.bracketDerivationSubmodule B ⊓ weightRaisingOperators b w)
      (fun X hX => ⟨OrthogonalBracketAlgebra.Construction.bracket_derivation_commutator B H X hH.2 hX.1,
        weightRaising_commutator_mem b H hH.1 w heig X hX.2⟩)
    rw [hspan]
    apply iSup_le
    intro r X hX
    have hXe : H * X - X * H = r • X := mem_eigenspace_iff.mp hX.2
    by_cases hr : 0 < r
    · exact InvolutionSpectralDecomposition.Construction.mem_positiveSpectralSubmodule _ _ hr hX.1.1 hXe
    · have hz := weightRaising_nonpositive_eigenvector_zero b H hH.1 w heig X hX.1.2 (le_of_not_gt hr) hXe
      rw [hz]
      exact Submodule.zero_mem _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationNilpotence.Construction
