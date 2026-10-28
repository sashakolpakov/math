import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCoordinates

/-! # Intrinsic Tensor Complex Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicTensorComplexCoordinates.CM

noncomputable section

/-! Complexification of the actual rational native tensor space and
normalization of paired CM components, with the Hermitian dual sign. -/

open scoped Classical _root_.NumberField Kronecker
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

theorem native_complex_phase_rational_tensor (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 m) :
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).complexPhase
      (fun i => ((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).rationalPhase (P.rational.coordinates x) i : ℂ)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents A (fun v j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j)) := by
  have hCoord := RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_coordinates A P
  have h := hCoord.2.2.2.2.2.2.1
    (fun v j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j))
  have he :
      (fun v j => A.real v ((P.localFrame (.inl (A.enumerate v))).coordinates
        (fun j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j)) j)) =
      (fun v j => A.real v (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (P.rational.coordinates x j))) := by
    funext v j
    rw [P.coordinates_compatible]
  rw [he] at h
  have hc : (fun i => ((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).realPhase
      (fun v j => A.real v (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (P.rational.coordinates x j))) i : ℂ)) =
      (fun i => ((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).rationalPhase (P.rational.coordinates x) i : ℂ)) := by
    funext i
    rw [hCoord.2.2.2.1]
    norm_cast
  rw [hc] at h
  exact h

def nativeTensorComponentNormalizer (v : Fin A.places) :
    Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℂ :=
  (A.basisV v).inv ⊗ₖ (A.basisP v).inv

def nativePairedTensorComponents : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A →ₗ[ℂ] RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase A where
  toFun w v :=
    ((nativeTensorComponentNormalizer A v).mulVec (w v).1,
      fun ij => (if v = A.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if A.positive v ij.2 then (1 : ℂ) else -1) *
        ((nativeTensorComponentNormalizer A v).map star).mulVec (w v).2 ij)
  map_add' x y := by
    funext v
    apply Prod.ext <;> funext ij <;>
      simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    funext v
    apply Prod.ext <;> funext ij <;>
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem native_real_tensor_components_of_values
    (t : ∀ v : Fin A.places, RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m)
    (w : Fin A.places → Fin 3 × Fin m → ℂ)
    (h : ∀ v j, A.complex v (t v j) = w v j) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents A t = nativePairedTensorComponents A
      (fun v => (w v, fun j => star (w v j))) := by
  funext v
  dsimp only [RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents, nativePairedTensorComponents, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [h]
  apply Prod.ext
  · rfl
  · funext ij
    exact congrArg (fun z : ℂ =>
      (if v = A.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if A.positive v ij.2 then (1 : ℂ) else -1) * z)
      (congrFun (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.conjugate_mulVec (nativeTensorComponentNormalizer A v) (w v)) ij)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicTensorComplexCoordinates.CM
