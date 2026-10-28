import OAI.RepresentationTheory.Theta.Adelic.TensorGeometricAction
import OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
import OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates

/-! # Intrinsic Geometric Action -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic

noncomputable section

/-! The actual native unitary tensor action becomes the specified
standard and inverse-transpose action in orthonormal complex coordinates. -/

open scoped Classical _root_.NumberField Kronecker

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.TensorGeometricAction OAI.RepresentationTheory.Theta.Adelic.GeometricGroup.UnitaryDualAction

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def nativeTensorAction (g : RationalSU.ArchimedeanSU F H)
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    ∀ v : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m :=
  fun v => Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))
    (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v)))
    (FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))) (s v)

theorem complex_native_tensor_action (g : RationalSU.ArchimedeanSU F H)
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) (v : Fin A.places) :
    (fun ij => A.complex v (nativeTensorAction A g s v ij)) =
      (((g (A.enumerate v)).val.val.map (A.complex v)) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)).mulVec (fun ij => A.complex v (s v ij)) := by
  let G := (g (A.enumerate v)).val.val
  have hM : Matrix.map
      (G ⊗ₖ (1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v)))))
      (A.complex v).toRingHom =
      G.map (A.complex v) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) := by
    apply Matrix.ext
    intro i j
    change A.complex v (G i.1 j.1 *
      (1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v)))) i.2 j.2) =
        A.complex v (G i.1 j.1) * (1 : Matrix (Fin m) (Fin m) ℂ) i.2 j.2
    by_cases h : i.2 = j.2 <;> simp [Matrix.one_apply, h]
  funext ij
  have h := (A.complex v).toRingHom.map_mulVec
    (G ⊗ₖ (1 : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v))))) (s v) ij
  rw [hM] at h
  exact h

theorem native_tensor_first (g : RationalSU.ArchimedeanSU F H)
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) (v : Fin A.places) :
    (BallGeometryData.realTensorComponents A (nativeTensorAction A g s) v).1 =
      (BallGeometryData.geometricAction A g (BallGeometryData.realTensorComponents A s) v).1 := by
  change ((A.basisV v).inv ⊗ₖ (A.basisP v).inv).mulVec
    (fun ij => A.complex v (nativeTensorAction A g s v ij)) = _
  rw [complex_native_tensor_action, TensorGeometricAction.tensor_conjugated_action]
  funext ij
  exact TensorGeometricAction.tensor_first_mulVec _ _ ij.1 ij.2

theorem native_geometric_action (g : RationalSU.ArchimedeanSU F H)
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    BallGeometryData.geometricAction A g (BallGeometryData.realTensorComponents A s) =
      BallGeometryData.realTensorComponents A (nativeTensorAction A g s) := by
  funext v
  apply Prod.ext
  · exact (native_tensor_first A g s v).symm
  · funext ij
    rcases ij with ⟨i, j⟩
    let U := GeometricGroup.standardUnit A v g
    let ss : Fin 3 → ℂ := fun k => if v = A.distinguished ∧ k = 2 then -1 else 1
    let c : ℂ := if A.positive v j then 1 else -1
    let x : Fin 3 → ℂ := fun k => (BallGeometryData.realTensorComponents A s v).1 (k, j)
    have hu : U.val.conjTranspose * Matrix.diagonal ss * U.val = Matrix.diagonal ss :=
      GeometricGroup.standardUnit_isometry A v g
    have hd := GeometricGroup.UnitaryDualAction.unitary_diagonal_dual U ss hu x c i
    have hi : U.inv = (BallGeometryData.standardMatrix A g v)⁻¹ := Matrix.coe_units_inv U
    rw [hi] at hd
    have hf : (BallGeometryData.realTensorComponents A (nativeTensorAction A g s) v).1 (i, j) =
        (BallGeometryData.standardMatrix A g v).mulVec x i := congrFun (native_tensor_first A g s v) (i, j)
    change ((BallGeometryData.standardMatrix A g v)⁻¹).transpose.mulVec (fun k => ss k * c * star (x k)) i =
      ss i * c * star ((BallGeometryData.realTensorComponents A (nativeTensorAction A g s) v).1 (i, j))
    rw [hf]
    exact hd

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic
