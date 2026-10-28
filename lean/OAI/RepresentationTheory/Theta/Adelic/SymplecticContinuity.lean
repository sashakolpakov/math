import OAI.RepresentationTheory.Theta.Adelic.GeometricActionContinuity

/-! # Symplectic Continuity -/

namespace OAI.RepresentationTheory.Theta.Adelic.SymplecticContinuity

noncomputable section

/-! Continuity of the actual real Siegel matrices and their blocks. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates.Symplectic OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.GeometricActionContinuity

theorem symplectic_blocks_continuous {G I : Type} [TopologicalSpace G]
    [Fintype I] [DecidableEq I]
    (e : G → ((I ⊕ I) → ℝ) ≃ₗ[ℝ] ((I ⊕ I) → ℝ))
    (hp : ∀ g x y, DataTheta.standardPairing (e g x) (e g y) = DataTheta.standardPairing x y)
    (he : Continuous (fun p : G × ((I ⊕ I) → ℝ) => e p.1 p.2)) :
    Continuous (fun g => DataTheta.blockMatrix (PoissonAutomorphyNormalizationData.blocks
      (BilinearCoordinates.Symplectic.linearSymplectic (BilinearCoordinates.Symplectic.swapConjugate (e g)) (BilinearCoordinates.Symplectic.swapConjugate_preserves (e g) (hp g))))) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [BilinearCoordinates.Symplectic.blocks_matrix, BilinearCoordinates.Symplectic.linearSymplectic_entry, BilinearCoordinates.Symplectic.swapConjugate_apply]
  have h := he.comp (continuous_id.prodMk (continuous_const (y := DataTheta.swapPhase (Pi.single j 1))))
  cases i with
  | inl i => exact (continuous_apply (.inr i)).comp h
  | inr i => exact (continuous_apply (.inl i)).comp h

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem realSymplecticBlocks_matrix_continuous :
    Continuous (fun g => DataTheta.blockMatrix (RealSymplecticAction.realSymplecticBlocks A P g)) :=
  symplectic_blocks_continuous (RealSymplecticAction.realCoordinateAction A P) (RealSymplecticAction.realCoordinateAction_preserves A P)
    (GeometricActionContinuity.realCoordinateAction_continuous A P)

theorem realSymplecticBlocks_C_continuous :
    Continuous (fun g => (RealSymplecticAction.realSymplecticBlocks A P g).C) := by
  have h := realSymplecticBlocks_matrix_continuous A P
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (.inl j)).comp ((continuous_apply (.inr i)).comp h)

theorem realSymplecticBlocks_D_continuous :
    Continuous (fun g => (RealSymplecticAction.realSymplecticBlocks A P g).D) := by
  have h := realSymplecticBlocks_matrix_continuous A P
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (.inr j)).comp ((continuous_apply (.inr i)).comp h)

end

end OAI.RepresentationTheory.Theta.Adelic.SymplecticContinuity
