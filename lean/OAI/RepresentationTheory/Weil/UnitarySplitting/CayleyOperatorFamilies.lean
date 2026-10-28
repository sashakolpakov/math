import OAI.RepresentationTheory.Weil.UnitarySplitting.LocallyConstantFourierFamilies
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyOperator

/-! # Cayley Operator Families -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyOperatorFamilies.Construction

noncomputable section

/-! Cayley operators on each Bruhat test vector vary locally constantly
with continuously varying invertible Cayley differences. -/

open _root_.MeasureTheory _root_.Topology Filter
open scoped InnerProductSpace

variable {F P : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [IsUltrametricDist F] [TopologicalSpace P] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
variable (g : P → FrameTransport.Construction.StandardSymplectic F d)
variable (D : P → Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
variable (hD : ∀ p x, D p x = (g p).val x - x)
variable (hDc : Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => D z.1 z.2))
variable (hDi : Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => (D z.1).symm z.2))

include hn hD hDc hDi in
theorem cayleyTestCoefficient_family_locallyConstant (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    IsLocallyConstant (fun p : P => WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient hF ψ hc hu ν (D p).toLinearEquiv f u) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
    let β := StandardTransvections.Construction.standardSymplecticBilinear F d
    let q : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F := fun z => CayleyCompositionPhase.Construction.cayleyWeylPhase β (D z.1).toLinearEquiv z.2
    have hqc : Continuous q := by
      change Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F d => BilinearFourierCoordinates.Construction.finiteBilinearContinuous β ((D z.1).symm z.2) z.2 / 2)
      fun_prop
    let e : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃L[F] Local.FunctionsMetaplectic.Construction.Position F (d + d) :=
      ContinuousLinearEquiv.piCongrLeft F (fun _ : Fin (d + d) => F) finSumFinEquiv
    let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val u.val
    have hCl : IsLocallyConstant C := UltraWeylCoefficients.Construction.weylMatrixCoefficient_locallyConstant_ultra hF ψ hc
      (Weak.Construction.referencePositionMeasure F d) f u
    have hCs : HasCompactSupport C := WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn
      (Weak.Construction.referencePositionMeasure F d) f u
    have hT := LocallyConstantFourierFamilies.Construction.chirpedBilinearFourierFamily_locallyConstant hF e β
      (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate d) ψ hc hn ν q hqc
      (fun p => (D p).symm.toHomeomorph) hDi hDc C hCl hCs
    have heq : (fun p : P => WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient hF ψ hc hu ν (D p).toLinearEquiv f u) =
        fun p => LocallyConstantFourierFamilies.Construction.chirpedBilinearFourierFamily ψ ν β q (fun p => (D p).symm) C p := by
      funext p v
      exact WeakCayleyCoefficients.Construction.weakCayleyGaussian_output_coefficient hF ψ hc hu ν (g p) (D p).toLinearEquiv (hD p) f u v
    rw [heq]
    exact hT

include hDc hDi in
theorem ultraCayleyOperator_family_locallyConstant (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    IsLocallyConstant (fun p : P => UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p) f) := by
  let u := LocalTest.Construction.ultraTestVector F hF d
  obtain ⟨r, hr, hres⟩ := WeylResolutionOperator.Construction.ultraResolution_positive_scalar hF ψ hc hu hn ν u (LocalTest.Construction.ultraTestVector_ne_zero F hF d)
  have hrep (p : P) : UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p) f =
      (r : ℂ)⁻¹ • CayleySynthesisPairing.Construction.ultraCayleySynthesis hF ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p) u f := by
    apply UltraCayleyOperator.Construction.testPairing_ext
    intro h
    rw [UltraCayleyOperator.Construction.ultraCayleyOperator_pairing]
    exact (CayleySynthesisPairing.Construction.ultraCayleySynthesis_normalized_pairing hF ψ hc hu hn ν (g p) (D p).toLinearEquiv
      (hD p) u r hr.ne' hres f h).symm
  have hcoeff := cayleyTestCoefficient_family_locallyConstant hF ψ hc hu hn ν g D hD hDc hDi f u
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  filter_upwards [hcoeff.eventually_eq p] with t ht
  rw [hrep t, hrep p]
  congr 1
  apply Subtype.ext
  change WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient hF ψ hc hu ν (D t).toLinearEquiv f u) u.val =
    WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient hF ψ hc hu ν (D p).toLinearEquiv f u) u.val
  rw [ht]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyOperatorFamilies.Construction
