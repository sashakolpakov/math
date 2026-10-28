import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallDatum
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Places
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum
import OAI.NumberTheory.ArithmeticGroups.Diagonal

/-! # Lagrangians -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Lagrangians.CM

noncomputable section

/-! Construct the two actual Hermitian multiplicity lines and their prescribed
positive holomorphic Lagrangian families. The pair uses one imaginary trace
coefficient and its literal orthogonal direct sum throughout. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

abbrev pairedAmbient (places : HeckeCycles.GeometricSource.CM.Places K) := Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin places.count)

def pairedBallForm (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) :=
  Geometry.ComplexBall.PrescribedSignsB.localB (HeckeCycles.ReferenceDatum.CM.embeddings K places) (Matrix.diagonal ![1, 1, B.b])

theorem paired_ball_domain (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) :
    {z : HeckeCycles.GeometricSource.CM.BallChart | (pairedBallForm K B places places.distinguished
      (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0} =
      B.domain := by
  ext z
  change (pairedBallForm K B places places.distinguished
    (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0 ↔ _
  rw [pairedBallForm, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real,
    HeckeCycles.ReferenceDatum.CM.embeddings_distinguished]
  change Complex.normSq (z 0) + Complex.normSq (z 1) +
    (B.b : ℂ).re * Complex.normSq 1 < 0 ↔ _
  simp only [Complex.normSq_one, mul_one]
  change _ ↔ Complex.normSq (z 0) + Complex.normSq (z 1) < -(B.b : ℂ).re
  constructor <;> intro h <;> linarith

structure LagrangianPair (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Fin places.count → Bool) where
  delta : K
  delta_ne_zero : delta ≠ 0
  delta_imaginary : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K delta = -delta
  a : Fin 2 → K
  a_sign : ∀ i, a i ≠ 0 ∧ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (a i) = a i ∧
    (HeckeCycles.ReferenceDatum.CM.embeddings K places places.distinguished (delta * a i)).im < 0
  family : Fin 2 → HeckeCycles.GeometricSource.CM.BallChart → Submodule ℂ (pairedAmbient K places)
  holomorphic : ∀ i, Geometry.ComplexBall.PrescribedSignsB.HolomorphicFamily B.domain
    (3 * places.count) (family i)
  prescribed_positive : ∀ i z, z ∈ B.domain →
    (∀ u, u ∈ family i z ↔ Geometry.ComplexBall.PrescribedSignsB.Prescribed (pairedBallForm K B places)
      places.distinguished (d i) z u) ∧
    Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * places.count)
      (Geometry.ComplexBall.PrescribedSignsB.tracePairing (pairedBallForm K B places)
        (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (delta * a i)))
      Geometry.ComplexBall.PrescribedSignsB.realConj (family i z)
  total_holomorphic : Geometry.ComplexBall.PrescribedSignsB.HolomorphicFamily B.domain
    ((3 * places.count) + (3 * places.count)) (fun z => (family 0 z).prod (family 1 z))
  total_positive : ∀ z, z ∈ B.domain →
    Geometry.ComplexBall.PrescribedSignsB.PositivePeriod ((3 * places.count) + (3 * places.count))
      (fun u v =>
        Geometry.ComplexBall.PrescribedSignsB.tracePairing (pairedBallForm K B places)
          (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (delta * a 0)) u.1 v.1 +
        Geometry.ComplexBall.PrescribedSignsB.tracePairing (pairedBallForm K B places)
          (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (delta * a 1)) u.2 v.2)
      (fun u => (Geometry.ComplexBall.PrescribedSignsB.realConj u.1, Geometry.ComplexBall.PrescribedSignsB.realConj u.2))
      ((family 0 z).prod (family 1 z))
  rational_trace : ∀ i (x y : HeckeCycles.GeometricSource.CM.Vec K),
    Geometry.ComplexBall.PrescribedSignsB.tracePairing (pairedBallForm K B places)
      (fun τ => HeckeCycles.ReferenceDatum.CM.embeddings K places τ (delta * a i))
      (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates (HeckeCycles.ReferenceDatum.CM.embeddings K places) x)
      (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates (HeckeCycles.ReferenceDatum.CM.embeddings K places) y) =
      (Algebra.trace ℚ K (delta * a i * HeckeCycles.GeometricSource.CM.hermitian K B.b x y) : ℂ)

theorem exists_lagrangian_pair (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Fin places.count → Bool) : Nonempty (LagrangianPair K B places d) := by
  have hWeakApproximation : Geometry.ComplexBall.PrescribedSignsB.WeakApproximationInput K := by
    intro ι hι v hn hd
    exact NumberTheory.Approximation.Weak.HodgeWeakApproximation.weak_approximation K v hn hd
  obtain ⟨δ, hδ, hδc⟩ := NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.exists_nonzero_imaginary
    (HeckeCycles.ReferenceDatum.CM.embeddings K places) places.distinguished
  have hneg : (pairedBallForm K B places places.distinguished
      ![0, 0, 1] ![0, 0, 1]).re < 0 := by
    simp only [pairedBallForm, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, mul_zero, mul_one, zero_add,
      HeckeCycles.ReferenceDatum.CM.embeddings_distinguished]
    exact B.negative
  have hcompact : ∀ i, i ≠ places.distinguished →
      ∀ x : Geometry.ComplexBall.PrescribedSignsB.Vec, x ≠ 0 →
        0 < (pairedBallForm K B places i x (star x)).re := by
    intro i hi
    exact NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_positive_definite (HeckeCycles.ReferenceDatum.CM.embeddings K places) B.b i
      ((HeckeCycles.ReferenceDatum.CM.source_signature K B places).2.2.2 i hi)
  obtain ⟨a, F, ha, hhol, hp, hsumhol, hsump, htrace⟩ :=
    Geometry.ComplexBall.PrescribedSignsB.lagrangians_with_prescribed_compact_place_signs hWeakApproximation
      (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) places.distinguished
      δ hδ hδc (Matrix.diagonal ![1, 1, B.b])
      (NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_hermitian B.b B.conjugate_b)
      (NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.diagonal_positive_plane (HeckeCycles.ReferenceDatum.CM.embeddings K places) B.b places.distinguished)
      hneg (fun i hi => Or.inl (hcompact i hi)) d
  have hO := paired_ball_domain K B places
  change {z | (Geometry.ComplexBall.PrescribedSignsB.localB (HeckeCycles.ReferenceDatum.CM.embeddings K places) (Matrix.diagonal ![1, 1, B.b])
    places.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z)
      (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0} = B.domain at hO
  rw [hO] at hhol hp hsumhol hsump
  simp only [Fintype.card_fin] at hhol hp hsumhol hsump
  refine ⟨⟨δ, hδ, hδc, a, ha, F, hhol, hp, hsumhol, hsump, ?_⟩⟩
  intro i x y
  have ht := htrace i x y
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.trace_matrix_diagonal] at ht
  exact ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Lagrangians.CM
