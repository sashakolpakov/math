import OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel

/-! # Regular Congruence Reflection -/

namespace OAI.RepresentationTheory.Theta.Adelic.RegularCongruenceReflection

noncomputable section

/-! An actual matrix congruence in the faithful six-dimensional
representation implies the literal two-coefficient quadratic congruence. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.UnitaryPolynomialEquations

variable (F : Type) [Field F] {d : F}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem principal_of_regular_congruence (N : ℕ) (g : SpecialUnitary.SU H.val)
    (hg : ∀ i j, ∃ a : 𝓞 F,
      (UnitaryPolynomialEquations.regularSU d H.val g).val i j - (1 : Matrix (Fin 6) (Fin 6) F) i j = (N : F) * (a : F)) :
    BallGeometryData.PrincipalLevel N g := by
  intro i j
  obtain ⟨a, ha⟩ := hg (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (i, 0)) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (j, 0))
  obtain ⟨b, hb⟩ := hg (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (i, 1)) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (j, 0))
  have h0 := Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_entry d (1 : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j 0 0
  have h1 := Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_entry d (1 : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j 1 0
  rw [map_one] at h0 h1
  change Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d g.val.val (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (i, 0)) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (j, 0)) -
    (1 : Matrix (Fin 6) (Fin 6) F) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (i, 0)) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (j, 0)) = _ at ha
  change Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d g.val.val (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (i, 1)) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (j, 0)) -
    (1 : Matrix (Fin 6) (Fin 6) F) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (i, 1)) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex (j, 0)) = _ at hb
  rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_entry, h0] at ha
  rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_entry, h1] at hb
  change (g.val.val i j).re - ((1 : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j).re =
    (N : F) * (a : F) at ha
  change (g.val.val i j).im - ((1 : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) i j).im =
    (N : F) * (b : F) at hb
  refine ⟨a, b, ?_⟩
  apply QuadraticAlgebra.ext
  · simpa using ha
  · simpa using hb

end

end OAI.RepresentationTheory.Theta.Adelic.RegularCongruenceReflection
