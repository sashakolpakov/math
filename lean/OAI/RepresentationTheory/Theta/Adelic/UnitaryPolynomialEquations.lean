import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData
import OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup

/-! # Unitary Polynomial Equations -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnitaryPolynomialEquations

noncomputable section

/-! Polynomial equations for the faithful six-dimensional representation
of the actual special-unitary group of an arbitrary Hermitian matrix. -/

open scoped Classical

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

section Ring
variable {R : Type*} [CommRing R]

def regularSU (d : R) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)) :
    SpecialUnitary.SU H →* Matrix.SpecialLinearGroup (Fin 6) R :=
  (Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularSpecialLinear d).comp (PrincipalSubgroup.suSpecialLinear H)

def unitaryImage (d : R) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 6) R) := (regularSU d H).range

def formError (d : R) (H M : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)) :
    Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) := M.conjTranspose * H * M - H

theorem unitaryImage_mem_iff (d : R) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d))
    (M : Matrix.SpecialLinearGroup (Fin 6) R) :
    M ∈ unitaryImage d H ↔
      Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M.val) = M.val ∧
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M.val).det = 1 ∧ formError d H (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M.val) = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    change Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d (Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d g.val.val)) = Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d g.val.val ∧
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d (Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d g.val.val)).det = 1 ∧
      formError d H (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d (Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d g.val.val)) = 0
    rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.decode_regularMatrix]
    exact ⟨rfl, congrArg Units.val g.property.2, sub_eq_zero.mpr g.property.1⟩
  · rintro ⟨hshape, hdet, hform⟩
    let A : Matrix.SpecialLinearGroup (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d) := ⟨Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M.val, hdet⟩
    let g : SpecialUnitary.SU H := ⟨Matrix.SpecialLinearGroup.toGL A,
      sub_eq_zero.mp hform, Matrix.SpecialLinearGroup.coeToGL_det A⟩
    exact ⟨g, Subtype.ext hshape⟩

def matrixEquation (d : R) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d))
    (M : Matrix (Fin 6) (Fin 6) R) : Geometry.ComplexBall.ArithmeticQuotientEquationsData.EquationIndex → R
  | .inl (i, j) => M i j - Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M) i j
  | .inr (.inl a) => Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticComponent a ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M).det - 1)
  | .inr (.inr ((i, j), a)) => Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticComponent a (formError d H (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M) i j)

theorem matrixEquation_zero_iff (d : R) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d))
    (M : Matrix.SpecialLinearGroup (Fin 6) R) :
    (∀ e, matrixEquation d H M.val e = 0) ↔ M ∈ unitaryImage d H := by
  rw [unitaryImage_mem_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply Matrix.ext
      intro i j
      exact (sub_eq_zero.mp (h (.inl (i, j)))).symm
    · apply sub_eq_zero.mp
      apply QuadraticAlgebra.ext
      · exact h (.inr (.inl 0))
      · exact h (.inr (.inl 1))
    · apply Matrix.ext
      intro i j
      apply QuadraticAlgebra.ext
      · exact h (.inr (.inr ((i, j), 0)))
      · exact h (.inr (.inr ((i, j), 1)))
  · rintro ⟨hshape, hdet, hform⟩ e
    rcases e with ⟨i, j⟩ | (a | ⟨⟨i, j⟩, a⟩) <;>
      simp [matrixEquation, hshape, hdet, hform, Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticComponent]

end Ring

variable {R S : Type*} [CommRing R] [CommRing S]

theorem formError_map (d : R) (H M : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)) (f : R →+* S) :
    (formError d H M).map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f) =
      formError (f d) (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f)) (M.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f)) := by
  change (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f).mapMatrix (M.conjTranspose * H * M - H) = _
  rw [map_sub, map_mul, map_mul]
  change M.conjTranspose.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f) * H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f) *
      M.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f) - H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f) = _
  rw [Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap_star d f)]
  rfl

theorem matrixEquation_map (d : R) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d))
    (f : R →+* S) (M : Matrix (Fin 6) (Fin 6) R) (e : Geometry.ComplexBall.ArithmeticQuotientEquationsData.EquationIndex) :
    f (matrixEquation d H M e) =
      matrixEquation (f d) (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f)) (M.map f) e := by
  rcases e with ⟨i, j⟩ | (a | ⟨⟨i, j⟩, a⟩)
  · have h := Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_map d f (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M)
    rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix_map] at h
    change f (M i j - Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M) i j) =
      f (M i j) - Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix (f d) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix (f d) (M.map f)) i j
    rw [map_sub, h]
    rfl
  · change f (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticComponent a ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M).det - 1)) = _
    rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticComponent_map, Geometry.ComplexBall.ArithmeticQuotientEquationsData.decode_determinant_map]
    rfl
  · have h := formError_map d H (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M) f
    rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix_map] at h
    change f (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticComponent a (formError d H (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d M) i j)) = _
    rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticComponent_map]
    exact congrArg (fun A : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic S (f d)) => Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticComponent a (A i j)) h

end

end OAI.RepresentationTheory.Theta.Adelic.UnitaryPolynomialEquations
