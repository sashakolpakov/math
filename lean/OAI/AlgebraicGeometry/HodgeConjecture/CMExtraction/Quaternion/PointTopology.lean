import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointOne
import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Point Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointTopology

noncomputable section

/-! Continuity of the quaternion subgroup map on actual local matrix
points, including the matrix inverse required by the unit-group topology. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction

variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

omit [IsTopologicalRing K] in
@[fun_prop]
theorem continuous_quadratic_mk {X : Type*} [TopologicalSpace X]
    (a : K) (f g : X → K) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (⟨f x, g x⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a)) :=
  (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff a _).mpr ⟨hf, hg⟩

theorem quaternionUnitaryCoordinateMatrix_continuous (a b : K) :
    Continuous (PointOne.quaternionUnitaryCoordinateMatrix a b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · change Continuous (fun x : Fin 4 → K => (⟨x 0, x 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a))
    fun_prop
  · exact continuous_const
  · change Continuous (fun x : Fin 4 → K =>
      -algebraMap K (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a) b * (⟨x 2, x 3⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a))
    fun_prop
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · change Continuous (fun x : Fin 4 → K => (⟨x 2, -x 3⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a))
    fun_prop
  · exact continuous_const
  · change Continuous (fun x : Fin 4 → K => (⟨x 0, -x 1⟩ : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K a))
    fun_prop

variable {F : Type} [Field F]

theorem quaternionPointUnitary_matrix_continuous (a b : F) (ρ : F →+* K) :
    Continuous (fun g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ =>
      (PointOne.quaternionPointUnitary a b ρ g).val.val) := by
  have hc : Continuous (fun g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ =>
      fun i => (NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm.matrixPointsHom (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) ρ g) i 0) := by
    apply continuous_pi
    intro i
    exact (continuous_apply 0).comp
      (Matrix.SpecialLinearGroup.continuous_apply
        (fun g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ => g.val)
        continuous_subtype_val i)
  exact ((quaternionUnitaryCoordinateMatrix_continuous (ρ a) (ρ b)).comp hc).congr
    (fun g => (PointOne.quaternionPointUnitary_matrix a b ρ g).symm)

theorem quaternionPointUnitary_continuous (a b : F) (ρ : F →+* K) :
    Continuous (PointOne.quaternionPointUnitary a b ρ) := by
  have hc := quaternionPointUnitary_matrix_continuous a b ρ
  apply continuous_induced_rng.mpr
  apply Units.continuous_iff.mpr
  refine ⟨hc, ?_⟩
  have hi := hc.comp (continuous_inv : Continuous
    (Inv.inv : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ → _))
  exact hi.congr (fun g => congrArg
    (fun x => x.val.val) (map_inv (PointOne.quaternionPointUnitary a b ρ) g))

def quaternionPointUnitaryContinuous (a b : F) (ρ : F →+* K) :
    (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).Points ρ →ₜ*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm
        (algebraMap K (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic K (ρ a)) (ρ b))) :=
  ⟨PointOne.quaternionPointUnitary a b ρ, quaternionPointUnitary_continuous a b ρ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointTopology
