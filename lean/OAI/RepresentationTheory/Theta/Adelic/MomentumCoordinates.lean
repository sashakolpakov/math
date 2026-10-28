import OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
import OAI.RepresentationTheory.Theta.Adelic.ArchimedeanTraceCoordinates
import OAI.RepresentationTheory.Theta.Adelic.CotangentCoordinates

/-! # Momentum Coordinates -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.MomentumCoordinates

/-! The momentum coordinates use the trace-dual integral basis.
Their real extension is the actual cotangent change of coordinates. -/

open scoped Classical _root_.NumberField

open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.ArchimedeanTraceCoordinates OAI.RepresentationTheory.Theta.Adelic.CotangentCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem real_coordinate_basis (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    CotangentCoordinates.coordinateBasis (MinkowskiCoordinatesPosition.realScalarCoordinates A).toLinearEquiv i =
      fun v => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (integralBasis F i)) := by
  apply (MinkowskiCoordinatesPosition.realScalarCoordinates A).injective
  change MinkowskiCoordinatesPosition.realScalarCoordinates A ((MinkowskiCoordinatesPosition.realScalarCoordinates A).symm ((Pi.basisFun ℝ _) i)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext j
  rw [MinkowskiCoordinatesPosition.realScalarCoordinates_rational]
  simp [Pi.basisFun_apply, Finsupp.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

def realScalarMomentumCoordinates :
    (Fin A.places → ℝ) ≃L[ℝ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) :=
  (CotangentCoordinates.cotangentCoordinates (MinkowskiCoordinatesPosition.realScalarCoordinates A).toLinearEquiv).toContinuousLinearEquiv

theorem realScalarMomentumCoordinates_rational (q : F)
    (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    realScalarMomentumCoordinates A (fun v =>
      A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) q)) i =
        ((integralBasis F).traceDual.repr q i : ℝ) := by
  change CotangentCoordinates.cotangentCoordinates (MinkowskiCoordinatesPosition.realScalarCoordinates A).toLinearEquiv _ i = _
  rw [CotangentCoordinates.cotangentCoordinates_apply, real_coordinate_basis,
    Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, ArchimedeanTraceCoordinates.trace_eq_sum_real_coordinates A]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul, map_mul]

theorem rational_scalar_pairing (x y : F) :
    ∑ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      (integralBasis F).repr x i * (integralBasis F).traceDual.repr y i =
        Algebra.trace ℚ F (x * y) := by
  have h := congrArg (Algebra.traceForm ℚ F y) ((integralBasis F).sum_repr x)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simp only [Module.Basis.traceDual_repr_apply]
  exact h.trans (by rw [Algebra.traceForm_apply, mul_comm])

theorem real_scalar_pairing (x y : Fin A.places → ℝ) :
    ∑ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      MinkowskiCoordinatesPosition.realScalarCoordinates A x i * realScalarMomentumCoordinates A y i =
        ∑ v, x v * y v :=
  CotangentCoordinates.coordinate_pairing (MinkowskiCoordinatesPosition.realScalarCoordinates A).toLinearEquiv x y

def rationalMomentumCoordinates : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (BallGeometryData.FrameIndex A → ℚ) :=
  (LinearEquiv.piCongrRight (fun _ : Fin (3 * m) => (integralBasis F).traceDual.equivFun)).trans
    (MinkowskiCoordinatesPosition.flattenCoordinates A ℚ)

def realMomentumCoordinates : BallGeometryData.RealPositions A ≃L[ℝ] (BallGeometryData.FrameIndex A → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv ((MinkowskiCoordinatesPosition.transposePositions A).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin (3 * m) =>
      (realScalarMomentumCoordinates A).toLinearEquiv)).trans (MinkowskiCoordinatesPosition.flattenCoordinates A ℝ)))

theorem rationalMomentumCoordinates_apply (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) (i : BallGeometryData.FrameIndex A) :
    rationalMomentumCoordinates A x i =
      (integralBasis F).traceDual.repr (x (finProdFinEquiv i.2))
        ((MinkowskiCoordinatesPosition.scalarIndexEquiv A).symm i.1) := rfl

theorem realMomentumCoordinates_apply (x : BallGeometryData.RealPositions A) (i : BallGeometryData.FrameIndex A) :
    realMomentumCoordinates A x i = realScalarMomentumCoordinates A
      (fun v => x v (finProdFinEquiv i.2)) ((MinkowskiCoordinatesPosition.scalarIndexEquiv A).symm i.1) := rfl

theorem realMomentumCoordinates_rational (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) (i : BallGeometryData.FrameIndex A) :
    realMomentumCoordinates A (BallGeometryData.archPositions A x) i =
      (rationalMomentumCoordinates A x i : ℝ) :=
  realScalarMomentumCoordinates_rational A _ _

end RepresentationTheory.Theta.Adelic.MomentumCoordinates

namespace RepresentationTheory.Theta.Adelic.MomentumCoordinates.PositionPairing

/-! The global position and momentum coordinates preserve respectively
the rational trace pairing and the sum of the real-place pairings. -/

open scoped Classical _root_.NumberField

open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.MomentumCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem flatten_pairing {R : Type*} [CommSemiring R]
    (x y : Fin (3 * m) → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → R) :
    ∑ i, MinkowskiCoordinatesPosition.flattenCoordinates A R x i * MinkowskiCoordinatesPosition.flattenCoordinates A R y i =
      ∑ j, ∑ k, x j k * y j k := by
  change (∑ i : BallGeometryData.FrameIndex A,
    (fun ji : Fin (3 * m) × Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
      x ji.1 ji.2 * y ji.1 ji.2) (MinkowskiCoordinatesPosition.frameCoefficientEquiv A i)) = _
  calc
    _ = ∑ ji : Fin (3 * m) × Module.Free.ChooseBasisIndex ℤ (𝓞 F),
        x ji.1 ji.2 * y ji.1 ji.2 :=
      Equiv.sum_comp (MinkowskiCoordinatesPosition.frameCoefficientEquiv A) (fun ji => x ji.1 ji.2 * y ji.1 ji.2)
    _ = _ := by rw [Fintype.sum_prod_type]

theorem rational_position_momentum_pairing (x y : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    ∑ i, MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i * rationalMomentumCoordinates A y i =
      Algebra.trace ℚ F (∑ j, x j * y j) := by
  change (∑ i, MinkowskiCoordinatesPosition.flattenCoordinates A ℚ (fun j => (integralBasis F).equivFun (x j)) i *
    MinkowskiCoordinatesPosition.flattenCoordinates A ℚ (fun j => (integralBasis F).traceDual.equivFun (y j)) i) = _
  rw [flatten_pairing]
  simp only [Module.Basis.equivFun_apply, rational_scalar_pairing]
  exact (map_sum (Algebra.trace ℚ F) _ _).symm

theorem real_position_momentum_pairing (x y : BallGeometryData.RealPositions A) :
    ∑ i, MinkowskiCoordinatesPosition.realPositionCoordinates A x i * realMomentumCoordinates A y i =
      ∑ v, ∑ j, x v j * y v j := by
  change (∑ i,
    MinkowskiCoordinatesPosition.flattenCoordinates A ℝ (fun j => MinkowskiCoordinatesPosition.realScalarCoordinates A (fun v => x v j)) i *
    MinkowskiCoordinatesPosition.flattenCoordinates A ℝ (fun j => realScalarMomentumCoordinates A (fun v => y v j)) i) = _
  rw [flatten_pairing]
  simp only [real_scalar_pairing]
  exact Finset.sum_comm

end RepresentationTheory.Theta.Adelic.MomentumCoordinates.PositionPairing

end

end OAI
