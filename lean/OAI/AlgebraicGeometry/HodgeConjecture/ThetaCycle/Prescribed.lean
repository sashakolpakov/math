import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Symplectic

/-! # Prescribed -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Prescribed.CM

noncomputable section

/-! Identify the constructed paired-embedding Lagrangians with the literal
Galois-indexed prescribed subspaces of the accepted HeckeCycles source predicate. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

theorem paired_form_eq_local (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (i : Fin places.count) (x y : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    Lagrangians.CM.pairedBallForm K B places i x y = HeckeCycles.GeometricSource.CM.localPairing K B.b (places.representative i) x y := by
  simp [Lagrangians.CM.pairedBallForm, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal, HeckeCycles.GeometricSource.CM.localPairing,
    HeckeCycles.ReferenceDatum.CM.embeddings, Fin.sum_univ_succ, add_assoc]

theorem paired_prescribed_iff (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    Geometry.ComplexBall.PrescribedSignsB.Prescribed (Lagrangians.CM.pairedBallForm K B places) places.distinguished
      (fun i => d (places.representative i)) z (Symplectic.CM.galoisToPaired K places w) ↔
        HeckeCycles.GeometricSource.CM.prescribed K B places d z w := by
  simp only [Geometry.ComplexBall.PrescribedSignsB.Prescribed, HeckeCycles.GeometricSource.CM.prescribed, Symplectic.CM.galoisToPaired_apply,
    paired_form_eq_local]
  rfl

theorem constructed_lagrangian_prescribed (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool)
    (P : Lagrangians.CM.LagrangianPair K B places (fun i j => d i (places.representative j)))
    (i : Fin 2) (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    Symplectic.CM.galoisToPaired K places w ∈ P.family i z ↔ HeckeCycles.GeometricSource.CM.prescribed K B places (d i) z w :=
  ((P.prescribed_positive i z hz).1 _).trans (paired_prescribed_iff K B places (d i) z w)

theorem paired_inverse_components (places : HeckeCycles.GeometricSource.CM.Places K) (u : Lagrangians.CM.pairedAmbient K places)
    (i : Fin places.count) :
    ((Symplectic.CM.galoisToPaired K places).symm u (places.representative i),
      (Symplectic.CM.galoisToPaired K places).symm u (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i)) = u i := by
  rw [← Symplectic.CM.galoisToPaired_apply, LinearEquiv.apply_symm_apply]

def nativePeriodFrame (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Gal(K/ℚ) → Bool)
    (z : HeckeCycles.GeometricSource.CM.BallChart) : (HeckeCycles.GeometricSource.CM.Positions K places → ℂ) →ₗ[ℂ] HeckeCycles.GeometricSource.CM.Ambient K :=
  (Symplectic.CM.galoisToPaired K places).symm.toLinearMap.comp
    (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB (HeckeCycles.ReferenceDatum.CM.embeddings K places) (Matrix.diagonal ![1, 1, B.b]))
      places.distinguished (fun i => d (places.representative i)) z)

/-- The accepted adapted coordinates recover exactly the coefficients of the
actual line/annihilator frame, including the compact-place choices. -/
theorem adapted_native_frame (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (v : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (nativePeriodFrame K B places d z v) = v := by
  funext p
  rcases p with ⟨i, j⟩
  let u := RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame
    (Geometry.ComplexBall.PrescribedSignsB.matrixB (HeckeCycles.ReferenceDatum.CM.embeddings K places) (Matrix.diagonal ![1, 1, B.b]))
    places.distinguished (fun i => d (places.representative i)) z v
  have h := paired_inverse_components K places u i
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  change (Symplectic.CM.galoisToPaired K places).symm u (places.representative i) = (u i).1 at hfirst
  change (Symplectic.CM.galoisToPaired K places).symm u (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i) = (u i).2 at hsecond
  change (if i = places.distinguished then
    if j = 0 then (Symplectic.CM.galoisToPaired K places).symm u (places.representative i) 2
    else (Symplectic.CM.galoisToPaired K places).symm u (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i) (j - 1)
    else if d (places.representative i) then
      (Symplectic.CM.galoisToPaired K places).symm u (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative i) j
    else (Symplectic.CM.galoisToPaired K places).symm u (places.representative i) j) = v (i, j)
  rw [hfirst, hsecond]
  by_cases hi : i = places.distinguished
  · subst i
    fin_cases j <;>
      simp [u, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame, Geometry.ComplexBall.PrescribedSignsB.globalFrame, Geometry.ComplexBall.PrescribedSignsB.placeFrame,
        Geometry.ComplexBall.PrescribedSignsB.localFrame, Geometry.ComplexBall.PrescribedSignsB.lineVector, Geometry.ComplexBall.PrescribedSignsB.axis]
  · cases hd : d (places.representative i) <;>
      simp [hi, hd, u, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame, Geometry.ComplexBall.PrescribedSignsB.globalFrame, Geometry.ComplexBall.PrescribedSignsB.placeFrame]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Prescribed.CM
