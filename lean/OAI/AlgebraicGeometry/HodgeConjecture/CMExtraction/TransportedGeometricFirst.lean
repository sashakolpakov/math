import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TransportedTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReindexedFrameGradient
import OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice

/-! # Transported Geometric First -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TransportedGeometricFirst.TestTransport

noncomputable section

/-! The transported first geometric tensor in a specified reindexed,
diagonally scaled frame. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d 1 H K}
variable (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A)
variable {I : Type} [Fintype I] [DecidableEq I]

def comparisonSlotVector (i : Fin 2) : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ :=
  Pi.single (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.slot (A := A) i) 1

theorem transported_geometricFirst_basis (e : I ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hZ : Z.matrix = (B.period z).matrix.submatrix e e)
    (c : I → ℂ) (L : Matrix I I ℂ)
    (hL : (B.frame z).val.submatrix e e * Matrix.diagonal c = L)
    (hdet : L.det ≠ 0) (i : I) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst B (Finite.BasisTransport.Test.transportBasisTest A B.rationalPosition (Finite.BasisTransport.Test.reindexFiniteTest e φ)) z
        (Pi.single (e i) 1) =
      (B.halfFrame z)⁻¹ * (c i * RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient L (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ Z) i) := by
  have hd := (TransportedTheta.TestTransport.transportedCompleted_hasFDerivAt B (Finite.BasisTransport.Test.reindexFiniteTest e φ) (B.period z)).fderiv
  rw [ReindexedTheta.TestTransport.reindexedFirst e φ Z (B.period z) hZ] at hd
  unfold RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.geometricFirst
  rw [hd]
  change (B.halfFrame z)⁻¹ *
    ((RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ Z).comp (ReindexedTheta.TestTransport.positionReindexLinear e ℂ))
      ((B.frame z).invᵀ *ᵥ Pi.single (e i) 1) = _
  rw [ReindexedFrameGradient.TestTransport.frameCovector_reindexed_scaled e (B.frame z) c L hL hdet]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TransportedGeometricFirst.TestTransport
