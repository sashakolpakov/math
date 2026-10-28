import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionActiveImage
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.AdelicClosure
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionApproximation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PositiveClosure

/-! # Adelic Binary Closure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AdelicBinaryClosure.Approximation

noncomputable section

/-! Quaternion strong approximation places every supported binary SL2
element in the closure of the original rational CM unitary group. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

abbrev CMHermitianAway := RestrictedAwaySame.Approximation.RestrictedAway
  (fun w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E) =>
    RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val (.inr w))
  (ActivePlace.Approximation.cmActivePlace E σ)

def cmActiveAwayRational : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b →*
    Matrix.SpecialLinearGroup (Fin 3) (Padic q) × CMHermitianAway E σ b hb hb0 δ hδ :=
  (ActiveAwayProjection.Approximation.activeAwayProjection (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
    (ActivePlace.Approximation.cmActivePlace E σ) (ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0))).toMonoidHom.comp
    ((RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)).comp
      (Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E δ hδ hδ0 b hb hb0).toMonoidHom)

theorem cmActiveAwayRational_first (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) :
    (cmActiveAwayRational E σ b hb hb0 δ hδ hδ0 g).1 = Matrix.SpecialLinearGroup.map σ g.val :=
  ActiveProjection.Approximation.cmActiveSL_original E σ δ hδ hδ0 b hb hb0 g

theorem cmActiveAwayRational_range :
    Set.range (fun z : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val =>
      ActiveAwayProjection.Approximation.activeAwayProjection (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
        (ActivePlace.Approximation.cmActivePlace E σ) (ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0))
        (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) z)) =
    Set.range (cmActiveAwayRational E σ b hb hb0 δ hδ hδ0) := by
  exact ((Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E δ hδ hδ0 b hb hb0).surjective.range_comp
    (fun z => ActiveAwayProjection.Approximation.activeAwayProjection (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
      (ActivePlace.Approximation.cmActivePlace E σ) (ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0))
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) z))).symm

variable [IsGalois ℚ E] (places : HeckeCycles.GeometricSource.CM.Places E)

theorem cm_binary_mem_closure
    (hball : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished b).re < 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) (Padic q)) :
    (Quaternion.QuadraticUnitary.activeBinaryBlock A, 1) ∈ closure (Set.range (cmActiveAwayRational E σ b hb hb0 δ hδ hδ0)) := by
  have h := Quaternion.PositiveClosure.quaternion_image_closure_of_positive (maximalRealSubfield E)
    (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
    (QuaternionActiveImage.Approximation.cmHermitianUnit_cm_scalar E b hb hb0 δ hδ hδ0) (ActivePlace.Approximation.cmActivePlace E σ)
    (G := Matrix.SpecialLinearGroup (Fin 3) (Padic q))
    (ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0))
    (ThetaCycle.QuadraticModel.CM.cm_quadratic_parameter_ne_zero E δ hδ hδ0)
    (QuaternionRealPlace.cmQuaternion_second_coefficient_ne_zero E b hb hb0)
    (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places places.distinguished)
    (ThetaCycle.CMArchimedeanCoordinates.CM.sourceRealCoordinate E places places.distinguished)
    (ThetaCycle.CMArchimedeanCoordinates.CM.source_real_coordinate_continuous E places places.distinguished)
    (QuaternionRealPlace.cmQuaternion_active_real_positive E places b hb hball) (Quaternion.QuadraticUnitary.activeBinaryBlock A)
    (QuaternionActiveImage.Approximation.cmQuaternion_canonical_image E b hb hb0 δ hδ hδ0 σ A)
  exact Eq.mp (congrArg (fun S => (Quaternion.QuadraticUnitary.activeBinaryBlock A, 1) ∈ closure S)
    (cmActiveAwayRational_range E σ b hb hb0 δ hδ hδ0)) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AdelicBinaryClosure.Approximation
