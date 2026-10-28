import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SparseFirst
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FrameProjection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta

/-! # Theta Spanning -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaSpanning.Multiplicity

noncomputable section

/-! Pointwise cotangent spanning for the actual normalized native theta
family. No nonvanishing or spanning assumption is added. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

theorem nativeCotangentProjection_surjective (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (hz : z ∈ P.domain) :
    Function.Surjective (CotangentTheta.Multiplicity.nativeCotangentProjection E P hP hμ v hv e he z) := by
  have hj : Function.Injective (fun i : Fin 2 => ((P.distinguished, i.succ) : Fin s × Fin 3)) := by
    intro i j h
    exact Fin.succ_inj.mp (congrArg Prod.snd h)
  exact FrameProjection.Multiplicity.scaled_frameProjection_surjective (ι := Fin s × Fin 3) _ hj (Multiplicity.Period.nativeLowerFrame E P hP v e z)
    (PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he z hz)
    (HolomorphicFrameRoot.Multiplicity.nativeFrameRootExtension E P hP hμ v hv e he z)⁻¹
    (inv_ne_zero (HolomorphicFrameRoot.Multiplicity.nativeFrameRootExtension_ne_zero E P hP hμ v hv e he z))

theorem nativeCotangentThetaOneForm_surjective (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (hz : z ∈ P.domain) :
    Function.Surjective (fun φ => CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he φ z) :=
  (nativeCotangentProjection_surjective E P hP hμ v hv e he z hz).comp
    (SparseFirst.nativeFirstTheta_surjective (ThetaCoordinates.Multiplicity.nativeThetaPeriod E P hP hμ v hv e he z))

theorem nativeCotangentTheta_exists_value (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (hz : z ∈ P.domain) :
    ∃ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3),
      CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he φ z (Pi.single 0 1) = 1 := by
  obtain ⟨φ, hφ⟩ := nativeCotangentThetaOneForm_surjective E P hP hμ v hv e he z hz
    (ContinuousLinearMap.proj (0 : Fin 2))
  exact ⟨φ, (congrArg (fun l : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent => l (Pi.single 0 1)) hφ).trans (by simp)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaSpanning.Multiplicity
