import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction

/-! # Theta Complex Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents.CM

noncomputable section

/-! The source CM components in the actual orthonormal tensor bases of
AdelicTheta. Both halves are complex linear in the original embedding components. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

def matrix (v : Fin places.count) : Matrix (Fin 3 × Fin 1) (Fin 3 × Fin 1) ℂ :=
  ((Source.BallArithmetic.CM.data E L).basisV v).inv ⊗ₖ
    ((Source.BallArithmetic.CM.data E L).basisP v).inv

def sign (v : Fin places.count) (ij : Fin 3 × Fin 1) : ℂ :=
  (if v = places.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
    (if (Source.BallArithmetic.CM.data E L).positive v ij.2 then (1 : ℂ) else -1)

def embeddingLinear (τ : Gal(E/ℚ)) : GeometricSource.CM.Ambient E →ₗ[ℂ] (Fin 3 × Fin 1 → ℂ) where
  toFun w ij := w τ ij.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def components : GeometricSource.CM.Ambient E →ₗ[ℂ] RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (Source.BallArithmetic.CM.data E L) :=
  LinearMap.pi (fun v =>
    ((Matrix.toLin' (matrix E L v)).comp (embeddingLinear E (places.representative v))).prod
      (LinearMap.pi (fun ij => sign E L v ij •
        ((LinearMap.proj ij).comp ((Matrix.toLin' ((matrix E L v).map star)).comp
          (embeddingLinear E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative v)))))))

theorem rational_coordinate (x : GeometricSource.CM.Vec E) (v : Fin places.count) (ij : Fin 3 × Fin 1) :
    (Source.BallArithmetic.CM.data E L).complex v
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (Source.QuadraticConjugation.CM.Field.RealField E)
        (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates))
        (.inl ((Source.BallArithmetic.CM.data E L).enumerate v))
        (Source.TensorPairing.CM.tensorVector E
          (OppositeCoordinates.CM.coordinates E L.coordinates) x ij)) =
      GeometricSource.CM.embeddingCoordinates E x (places.representative v) ij.1 := by
  change Source.ArchimedeanCoordinates.CM.complexCoordinate E
    (OppositeCoordinates.CM.coordinates E L.coordinates) v
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (Source.QuadraticConjugation.CM.Field.RealField E) _ _
      ((Source.QuadraticConjugation.CM.Field.fieldEquiv E (OppositeCoordinates.CM.coordinates E L.coordinates)).symm (x ij.1))) = _
  rw [Source.ArchimedeanCoordinates.CM.rational_compatibility, AlgEquiv.apply_symm_apply]
  rfl

theorem rational (x : GeometricSource.CM.Vec E) :
    components E L (GeometricSource.CM.embeddingCoordinates E x) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents (Source.BallArithmetic.CM.data E L) (fun v ij =>
        RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (Source.QuadraticConjugation.CM.Field.RealField E)
          (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates))
          (.inl ((Source.BallArithmetic.CM.data E L).enumerate v))
          (Source.TensorPairing.CM.tensorVector E
            (OppositeCoordinates.CM.coordinates E L.coordinates) x ij)) := by
  have he (v : Fin places.count) :
      (fun ij : Fin 3 × Fin 1 => GeometricSource.CM.embeddingCoordinates E x
        (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative v) ij.1) =
      fun ij => star (GeometricSource.CM.embeddingCoordinates E x (places.representative v) ij.1) := by
    funext ij
    exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe E (places.representative v (x ij.1))
  funext v
  change Fin places.count at v
  apply Prod.ext
  · exact congrArg (Matrix.mulVec (matrix E L v))
      (funext fun ij => (rational_coordinate E L x v ij).symm)
  · funext ij
    change sign E L v ij * (((matrix E L v).map star).mulVec _) ij =
      sign E L v ij * star ((matrix E L v).mulVec _ ij)
    congr 1
    change ((matrix E L v).map star).mulVec
      (fun kl => GeometricSource.CM.embeddingCoordinates E x (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative v) kl.1) ij = _
    rw [he, ← RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.conjugate_mulVec]
    apply congrArg star
    apply congrArg (fun f : (Fin 3 × Fin 1) → ℂ => (matrix E L v).mulVec f ij)
    funext kl
    exact (rational_coordinate E L x v kl).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents.CM
