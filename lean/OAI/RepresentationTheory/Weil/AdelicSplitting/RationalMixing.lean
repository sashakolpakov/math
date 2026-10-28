import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryAlgebra
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Rational Mixing -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalMixing.Construction

noncomputable section

/-! Some rational unitary-pair element mixes momentum into position in
any polarization of a positive-dimensional tensor space. -/

open scoped Classical Kronecker

def momentumSubspace (F : Type*) [Field F] (N : ℕ) :
    Submodule F ((Fin N ⊕ Fin N) → F) where
  carrier := {x | ∀ i, x (.inl i) = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; simp [hx i, hy i]
  smul_mem' := by intro s x hx i; simp [hx i]

theorem dualPairSymplectic_mulVec_coordinates
    {F : Type*} [Field F] {d : F} {n m : ℕ}
    (H : Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))
    (K : Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))
    (c : TensorSpace.Construction.SymplecticFrame d n m H K) (g : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K)
    (x : TensorSpace.Construction.TensorPosition d n m) :
    (TensorSpace.Construction.dualPairSymplectic H K c g).val.mulVec (c.coordinates x) =
      c.coordinates ((g.1.val.val ⊗ₖ g.2.val.val).mulVec x) := by
  change (LinearMap.toMatrix' (TensorSpace.Construction.coordinateAction H K c g).toLinearMap).mulVec (c.coordinates x) = _
  rw [LinearMap.toMatrix'_mulVec]
  change c.coordinates (TensorSpace.Construction.tensorLinear H K g (c.coordinates.symm (c.coordinates x))) = _
  rw [c.coordinates.symm_apply_apply]
  rfl

theorem exists_rational_unitary_mixing
    {F : Type*} [Field F] [CharZero F] (d : F) (hd : ¬ IsSquare d)
    (n m : ℕ) (hN : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (c : TensorSpace.Construction.SymplecticFrame d n m H.val K.val) :
    ∃ (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) (i j : Fin (n * m)),
      (TensorSpace.Construction.dualPairSymplectic H.val K.val c g).val (.inl i) (.inr j) ≠ 0 := by
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := ⟨by
    intro r hr
    apply hd
    refine ⟨r, ?_⟩
    simpa [sq] using hr.symm⟩
  by_contra! hzero
  let L : Submodule F (TensorSpace.Construction.TensorPosition d n m) :=
    (momentumSubspace F (n * m)).comap c.coordinates.toLinearMap
  have hInv (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) (x : TensorSpace.Construction.TensorPosition d n m) (hx : x ∈ L) :
      (g.1.val.val ⊗ₖ g.2.val.val).mulVec x ∈ L := by
    change ∀ i, (c.coordinates ((g.1.val.val ⊗ₖ g.2.val.val).mulVec x)) (.inl i) = 0
    rw [← dualPairSymplectic_mulVec_coordinates]
    have hx' : ∀ i, (c.coordinates x) (.inl i) = 0 := hx
    intro i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hx', hzero]
  let δ : UnitaryBase.Construction.Quadratic F d := ⟨0, 1⟩
  have hδ : star δ = -δ := by
    ext <;> simp [δ]
  have hδ0 : δ ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg QuadraticAlgebra.im h)
  have hF (s : F) : star (algebraMap F (UnitaryBase.Construction.Quadratic F d) s) = algebraMap F (UnitaryBase.Construction.Quadratic F d) s := by
    ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  have hStab : UnitaryAlgebra.Construction.matrixSubmoduleStabilizer L = ⊤ :=
    UnitaryAlgebra.Construction.unitary_tensor_subalgebra_eq_top (F := F) hF δ hδ hδ0 H hH K hK
      (UnitaryAlgebra.Construction.matrixSubmoduleStabilizer L) hInv
  have hcases := UnitaryAlgebra.Construction.eq_bot_or_top_of_matrix_stabilizer_top L hStab
  let i : Fin (n * m) := ⟨0, hN⟩
  let p : TensorSpace.Construction.StandardPhase (k := F) n m := Pi.single (.inr i) 1
  let q : TensorSpace.Construction.StandardPhase (k := F) n m := Pi.single (.inl i) 1
  have hp : c.coordinates.symm p ∈ L := by
    change ∀ j, (c.coordinates (c.coordinates.symm p)) (.inl j) = 0
    rw [c.coordinates.apply_symm_apply]
    intro j
    simp [p]
  have hpn : c.coordinates.symm p ≠ 0 := by
    intro hz
    have h := congrArg (fun x => c.coordinates x (.inr i)) hz
    simp [p] at h
  have hq : c.coordinates.symm q ∉ L := by
    intro hx
    have h : (c.coordinates (c.coordinates.symm q)) (.inl i) = 0 := hx i
    simp [q] at h
  rcases hcases with hb | ht
  · apply hpn
    simpa only [hb, Submodule.mem_bot] using hp
  · exact hq (ht ▸ (show c.coordinates.symm q ∈ (⊤ : Submodule F (TensorSpace.Construction.TensorPosition d n m)) from trivial))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalMixing.Construction
