import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase
import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Tensor Space -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction

noncomputable section

/-! The symplectic action of the full unitary pair on its actual trace
tensor space. A symplectic frame is only a choice of linear coordinates. -/

open scoped Classical Kronecker
open _root_.Matrix

section Sesquilinear
variable {R : Type*} [CommRing R] [StarRing R]
  {I : Type*} [Fintype I] [DecidableEq I]

def formValue (H : Matrix I I R) (x y : I → R) : R :=
  dotProduct (fun i => star (x i)) (H.mulVec y)

omit [DecidableEq I] in
theorem conjugate_mulVec (A : Matrix I I R) (x : I → R) :
    (fun i => star (A.mulVec x i)) = (A.map star).mulVec (fun i => star (x i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, star_sum]

omit [DecidableEq I] in
theorem formValue_change (H A : Matrix I I R) (x y : I → R) :
    formValue H (A.mulVec x) (A.mulVec y) = formValue (A.conjTranspose * H * A) x y := by
  unfold formValue
  rw [conjugate_mulVec]
  simp only [Matrix.conjTranspose, Matrix.mulVec_mulVec, dotProduct_mulVec]
  rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  rw [Matrix.transpose_map]

theorem formValue_unitary (H : Matrix I I R) (g : UnitaryBase.Construction.Unitary H) (x y : I → R) :
    formValue H (g.val.val.mulVec x) (g.val.val.mulVec y) = formValue H x y := by
  rw [formValue_change, g.property]

end Sesquilinear

variable {k : Type*} [Field k] (d : k) (n m : ℕ)

abbrev TensorPosition := Fin n × Fin m → UnitaryBase.Construction.Quadratic k d
abbrev StandardPhase := (Fin (n * m) ⊕ Fin (n * m)) → k

def tracePairing (H : Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic k d))
    (K : Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic k d))
    (x y : TensorPosition d n m) : k :=
  QuadraticAlgebra.trace (formValue (H ⊗ₖ K) x y) / 2

def coordinatePairing (x y : StandardPhase (k := k) n m) : k :=
  -(Matrix.J (Fin (n * m)) k).toBilin' x y

structure SymplecticFrame (H : Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic k d))
    (K : Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic k d)) where
  coordinates : TensorPosition d n m ≃ₗ[k] StandardPhase (k := k) n m
  preserves : ∀ x y, coordinatePairing n m (coordinates x) (coordinates y) =
    tracePairing d n m H K x y

variable {d n m}
  (H : Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic k d))
  (K : Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic k d))

def tensorLinear (g : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K) :
    TensorPosition d n m ≃ₗ[k] TensorPosition d n m :=
  (Matrix.GeneralLinearGroup.toLin (UnitaryBase.Construction.unitaryTensor H K g).val).toLinearEquiv.restrictScalars k

theorem tensorLinear_preserves (g : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K) (x y : TensorPosition d n m) :
    tracePairing d n m H K (tensorLinear H K g x) (tensorLinear H K g y) =
      tracePairing d n m H K x y := by
  unfold tracePairing
  exact congrArg (fun z : UnitaryBase.Construction.Quadratic k d => QuadraticAlgebra.trace z / 2)
    (formValue_unitary (H ⊗ₖ K) (UnitaryBase.Construction.unitaryTensor H K g) x y)

def coordinateAction (c : SymplecticFrame d n m H K) (g : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K) :
    StandardPhase (k := k) n m ≃ₗ[k] StandardPhase (k := k) n m :=
  c.coordinates.symm.trans ((tensorLinear H K g).trans c.coordinates)

theorem coordinateAction_preserves (c : SymplecticFrame d n m H K)
    (g : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K) (x y : StandardPhase (k := k) n m) :
    coordinatePairing n m (coordinateAction H K c g x) (coordinateAction H K c g y) =
      coordinatePairing n m x y := by
  change coordinatePairing n m
    (c.coordinates (tensorLinear H K g (c.coordinates.symm x)))
    (c.coordinates (tensorLinear H K g (c.coordinates.symm y))) = _
  rw [c.preserves, tensorLinear_preserves, ← c.preserves]
  simp

def coordinateMatrix (c : SymplecticFrame d n m H K) (g : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K) :=
  LinearMap.toMatrix' (coordinateAction H K c g).toLinearMap

theorem coordinateMatrix_symplectic (c : SymplecticFrame d n m H K)
    (g : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K) :
    coordinateMatrix H K c g ∈ Matrix.symplecticGroup (Fin (n * m)) k := by
  apply SymplecticGroup.mem_iff'.mpr
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp]
  simp only [coordinateMatrix, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have h := coordinateAction_preserves H K c g x y
  have h' := congrArg (fun a : k => -a) h
  simpa [coordinatePairing] using h'

/-- The actual tensor-product symplectic matrix, in the chosen polarization. -/
def dualPairSymplectic (c : SymplecticFrame d n m H K) :
    UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K →* Matrix.symplecticGroup (Fin (n * m)) k where
  toFun g := ⟨coordinateMatrix H K c g, coordinateMatrix_symplectic H K c g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearMap.toMatrix'.symm.injective
    ext x i
    simp [coordinateMatrix, coordinateAction, tensorLinear]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearMap.toMatrix'.symm.injective
    ext x i
    simp [coordinateMatrix, coordinateAction, tensorLinear, map_mul,
      Matrix.mulVec_mulVec]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction
