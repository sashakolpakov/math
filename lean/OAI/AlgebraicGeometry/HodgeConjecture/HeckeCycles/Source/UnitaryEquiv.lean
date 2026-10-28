import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryMatrix

/-! # Unitary Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEquiv.CM

noncomputable section

/-! The source rational group and the quadratic-algebra special-unitary
group are isomorphic through the original field coordinates. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryMatrix.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)

def originalSL : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QuadraticForms.CM.hermitianForm E Q).val →*
    Matrix.SpecialLinearGroup (Fin 3) E where
  toFun g := ⟨g.val.val.map (QuadraticConjugation.CM.Field.fieldEquiv E Q), by
    change ((QuadraticConjugation.CM.Field.fieldEquiv E Q).toRingHom.mapMatrix g.val.val).det = 1
    rw [← RingHom.map_det]
    have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
    rw [hd, map_one]⟩
  map_one' := by
    apply Subtype.ext
    change (QuadraticConjugation.CM.Field.fieldEquiv E Q).toRingHom.mapMatrix 1 = 1
    exact map_one _
  map_mul' g h := by
    apply Subtype.ext
    change (QuadraticConjugation.CM.Field.fieldEquiv E Q).toRingHom.mapMatrix (g.val.val * h.val.val) =
      (QuadraticConjugation.CM.Field.fieldEquiv E Q).toRingHom.mapMatrix g.val.val * (QuadraticConjugation.CM.Field.fieldEquiv E Q).toRingHom.mapMatrix h.val.val
    exact map_mul _ _ _

theorem vector_action (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QuadraticForms.CM.hermitianForm E Q).val) (x : GeometricSource.CM.Vec E) :
    g.val.val *ᵥ UnitaryMatrix.CM.vector E Q x = UnitaryMatrix.CM.vector E Q (Matrix.SpecialLinearGroup.toLin' (originalSL E Q g) x) := by
  funext i
  change (∑ j, g.val.val i j * (QuadraticConjugation.CM.Field.fieldEquiv E Q).symm (x j)) =
    (QuadraticConjugation.CM.Field.fieldEquiv E Q).symm (∑ j, QuadraticConjugation.CM.Field.fieldEquiv E Q (g.val.val i j) * x j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, AlgEquiv.symm_apply_apply]

theorem original_preserves (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QuadraticForms.CM.hermitianForm E Q).val) (x y : GeometricSource.CM.Vec E) :
    GeometricSource.CM.hermitian E B.b (Matrix.SpecialLinearGroup.toLin' (originalSL E Q g) x)
      (Matrix.SpecialLinearGroup.toLin' (originalSL E Q g) y) = GeometricSource.CM.hermitian E B.b x y := by
  rw [← UnitaryMatrix.CM.form_image E Q, ← vector_action, ← vector_action]
  have hg := RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue_unitary (QuadraticForms.CM.hermitianForm E Q).val
    (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary _ g) (UnitaryMatrix.CM.vector E Q y) (UnitaryMatrix.CM.vector E Q x)
  change RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (QuadraticForms.CM.hermitianForm E Q).val (g.val.val *ᵥ UnitaryMatrix.CM.vector E Q y) (g.val.val *ᵥ UnitaryMatrix.CM.vector E Q x) = _ at hg
  rw [hg, UnitaryMatrix.CM.form_image]

def inverse : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QuadraticForms.CM.hermitianForm E Q).val →* Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b where
  toFun g := ⟨originalSL E Q g, original_preserves E Q g⟩
  map_one' := Subtype.ext (map_one (originalSL E Q))
  map_mul' g h := Subtype.ext (map_mul (originalSL E Q) g h)

theorem inverse_hom (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : inverse E Q (UnitaryMatrix.CM.hom E Q g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact (QuadraticConjugation.CM.Field.fieldEquiv E Q).apply_symm_apply (g.val.val i j)

theorem hom_inverse (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QuadraticForms.CM.hermitianForm E Q).val) :
    UnitaryMatrix.CM.hom E Q (inverse E Q g) = g := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact (QuadraticConjugation.CM.Field.fieldEquiv E Q).symm_apply_apply (g.val.val i j)

def equivalence : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b ≃*
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (QuadraticForms.CM.hermitianForm E Q).val where
  toFun := UnitaryMatrix.CM.hom E Q
  invFun := inverse E Q
  left_inv := inverse_hom E Q
  right_inv := hom_inverse E Q
  map_mul' := (UnitaryMatrix.CM.hom E Q).map_mul

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEquiv.CM
