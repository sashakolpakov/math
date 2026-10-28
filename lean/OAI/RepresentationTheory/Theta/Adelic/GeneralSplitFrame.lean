import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction

/-! # General Split Frame -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeneralSplitFrame

noncomputable section

/-! The stable polarization of the full split tensor product, in arbitrary
dimensions and with the actual trace symplectic pairing. -/

open scoped Kronecker

open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitAction.Coordinates

variable {k : Type} [Field k] [CharZero k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0) (n m : ℕ)

def positionReindex : ((Fin n × Fin m) → k) ≃ₗ[k] (Fin (n * m) → k) where
  toFun x := x ∘ finProdFinEquiv.symm
  invFun x := x ∘ finProdFinEquiv
  left_inv x := by funext i; exact congrArg x (finProdFinEquiv.symm_apply_apply i)
  right_inv x := by funext i; exact congrArg x (finProdFinEquiv.apply_symm_apply i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharZero k] in
theorem positionReindex_dot (x y : (Fin n × Fin m) → k) :
    dotProduct (positionReindex (k := k) n m x) (positionReindex n m y) = dotProduct x y := by
  change dotProduct (x ∘ finProdFinEquiv.symm) (y ∘ finProdFinEquiv.symm) = _
  exact comp_equiv_dotProduct_comp_equiv x y finProdFinEquiv.symm

variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)

def phaseCoordinates : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m ≃ₗ[k] Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m :=
  (GeneralSplitAction.Coordinates.polarizedCoordinates r hr hr0 (Fin n × Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K)).trans
    (((positionReindex (k := k) n m).prodCongr (positionReindex n m)).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin (n * m)) (Fin (n * m)) k k).symm)

theorem phaseCoordinates_apply (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    phaseCoordinates r hr hr0 n m H K x =
      Sum.elim (positionReindex n m (GeneralSplitAction.Coordinates.polarizedCoordinates r hr hr0 (Fin n × Fin m)
          (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K) x).1)
        (positionReindex n m (GeneralSplitAction.Coordinates.polarizedCoordinates r hr hr0 (Fin n × Fin m)
          (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K) x).2) := rfl

omit [CharZero k] in
theorem coordinatePairing_sumElim (q p q' p' : Fin (n * m) → k) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m (Sum.elim q p) (Sum.elim q' p') =
      dotProduct q p' - dotProduct p q' := by
  simp [Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing, Matrix.J, Matrix.toBilin'_apply, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
  ring

omit [CharZero k] in
theorem tensor_skew (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K).val.conjTranspose = -(Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K).val := by
  change (H.val ⊗ₖ K.val).conjTranspose = -(H.val ⊗ₖ K.val)
  rw [Matrix.conjTranspose_kronecker, hH, hK]
  apply Matrix.ext
  intro i j
  change H.val i.1 j.1 * -(K.val i.2 j.2) = -(H.val i.1 j.1 * K.val i.2 j.2)
  exact mul_neg _ _

theorem phaseCoordinates_preserves
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (x y : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m (phaseCoordinates r hr hr0 n m H K x)
        (phaseCoordinates r hr hr0 n m H K y) = Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d n m H.val K.val x y := by
  rw [phaseCoordinates_apply, phaseCoordinates_apply, coordinatePairing_sumElim,
    positionReindex_dot, positionReindex_dot]
  exact GeneralSplitAction.Coordinates.polarizedCoordinates_preserves r hr hr0 (Fin n × Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits H K)
    (tensor_skew n m H K hH hK) x y

def splitFrame (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H.val K.val where
  coordinates := phaseCoordinates r hr hr0 n m H K
  preserves := phaseCoordinates_preserves r hr hr0 n m H K hH hK

end

end OAI.RepresentationTheory.Theta.Adelic.GeneralSplitFrame
