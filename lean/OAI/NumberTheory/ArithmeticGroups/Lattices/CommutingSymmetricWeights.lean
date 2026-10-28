import OAI.NumberTheory.ArithmeticGroups.Lattices.SimultaneousOrthonormalEigenbasis
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketAlgebra

/-! # Commuting Symmetric Weights -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingSymmetricWeights.Construction

noncomputable section

/-! Simultaneous eigenvalues of a commuting symmetric operator
subspace are linear functionals on that subspace. -/

open scoped Classical

theorem exists_commuting_symmetric_weights
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (a : Submodule ℝ (L →L[ℝ] L))
    (ha : ∀ A ∈ a, A.toLinearMap.IsSymmetric)
    (hc : ∀ A ∈ a, ∀ C ∈ a, Commute A C) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℝ L)) ℝ L)
      (w : Fin (Module.finrank ℝ L) → Module.Dual ℝ a),
      ∀ i (A : a), A.val (b i) = w i A • b i := by
  let T : a → L →ₗ[ℝ] L := fun A => A.val.toLinearMap
  have hT (A : a) : (T A).IsSymmetric := ha A.val A.property
  have hcomm : Pairwise (fun A C => Commute (T A) (T C)) := fun A C _ =>
    congrArg ContinuousLinearMap.toLinearMap (hc A.val A.property C.val C.property).eq
  obtain ⟨b, v, hv⟩ := SimultaneousOrthonormalEigenbasis.Construction.exists_simultaneous_orthonormal_eigenbasis T hT hcomm
  let w : Fin (Module.finrank ℝ L) → Module.Dual ℝ a := fun i =>
    (b.toBasis.coord i).comp ((ContinuousLinearMap.apply ℝ L (b i)).toLinearMap.comp a.subtype)
  refine ⟨b, w, fun i A => ?_⟩
  have hw : w i A = v i A := by
    change b.toBasis.repr (A.val (b i)) i = v i A
    rw [show A.val (b i) = v i A • b i from hv i A]
    simp only [map_smul, Finsupp.smul_apply]
    have hi : b.toBasis.repr (b i) i = 1 :=
      (b.toBasis.repr_self_apply i i).trans (ite_eq_left rfl)
    rw [hi, smul_eq_mul, mul_one]
  rw [hw]
  exact hv i A

theorem orthonormal_eigen_coordinate
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [Fintype ι]
    (b : OrthonormalBasis ι ℝ L) (A : L →L[ℝ] L) (hA : A.toLinearMap.IsSymmetric)
    (w : ι → ℝ) (heig : ∀ i, A (b i) = w i • b i) (x : L) (i : ι) :
    b.repr (A x) i = w i * b.repr x i := by
  rw [b.repr_apply_apply, b.repr_apply_apply]
  calc
    inner ℝ (b i) (A x) = inner ℝ (A (b i)) x := (hA (b i) x).symm
    _ = w i * inner ℝ (b i) x := by rw [heig, real_inner_smul_left]

theorem bracket_structure_coefficient_weight
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L] [Fintype ι]
    (B : L →L[ℝ] L →L[ℝ] L) (a : Submodule ℝ (L →L[ℝ] L))
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (b : OrthonormalBasis ι ℝ L)
    (w : ι → Module.Dual ℝ a) (heig : ∀ i (A : a), A.val (b i) = w i A • b i)
    (i j r : ι) (hc : b.repr (B (b i) (b j)) r ≠ 0) : w r = w i + w j := by
  ext A
  have hA := ha A.property
  have hd := (OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B A.val).mp hA.2 (b i) (b j)
  have he := congrArg (fun x => b.repr x r) hd
  rw [orthonormal_eigen_coordinate b A.val hA.1 (fun s => w s A) (fun s => heig s A),
    heig, heig] at he
  simp only [map_add, map_smul, smul_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul] at he
  change w r A = w i A + w j A
  apply mul_right_cancel₀ hc
  rw [add_mul]
  exact he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingSymmetricWeights.Construction
