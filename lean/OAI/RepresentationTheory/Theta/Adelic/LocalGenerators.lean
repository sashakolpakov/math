import OAI.RepresentationTheory.Theta.Adelic.LocalConstancy
import OAI.RepresentationTheory.Theta.Adelic.LocalKernel
import OAI.RepresentationTheory.Theta.Adelic.BigCellOne
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner

/-! # Local Generators -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalGenerators

noncomputable section

/-! Genuine local oscillator lifts of the Gauss-coordinate generators.
Their existence uses checked function-space and Fourier constructions,
not an assumption of a splitting or a smooth representation. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing.Construction
open OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis
open OAI.RepresentationTheory.Theta.Adelic.BigCellOne OAI.RepresentationTheory.Theta.Adelic.LocalConstancy
open OAI.RepresentationTheory.Theta.Adelic.LocalKernel Filter
open scoped _root_.Topology

variable {k : Type} [NormedField k] [IsUltrametricDist k] [CharZero k]
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {N : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t : k => ψ t))
    (hu : ∀ t : k, ‖ψ t‖ = 1)

include hc in
omit [CharZero k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
  [SecondCountableTopology k] in
theorem quadratic_preserves_test (B : Matrix (Fin N) (Fin N) k)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  obtain ⟨hf, hs⟩ := Weil.UnitarySplitting.UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
  apply Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · exact ((Weil.UnitarySplitting.LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous
      (show Continuous (Weil.Local.FunctionsMetaplectic.Construction.quadratic B) by unfold Weil.Local.FunctionsMetaplectic.Construction.quadratic; fun_prop)).mul hf
  · exact hs.mul_left

def quadraticLift (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N) : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ :=
  Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.quadraticOscillator ψ (quadratic_preserves_test ψ hc) hu B

omit [SecondCountableTopology k] in
theorem quadraticLift_projection (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N) :
    Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (quadraticLift ψ hc hu B) = Weil.Local.Generators.Construction.quadraticSymplectic B := rfl

omit [SecondCountableTopology k] in
theorem quadraticLift_apply (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (quadraticLift ψ hc hu B) f).val =
      Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B.val f.val := rfl

omit [IsUltrametricDist k] [CharZero k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem phaseRotation_eq_weyl (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    Weil.UnitarySplitting.FourierCovariance.Construction.fourierPhaseRotation v = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.weylSymplectic k N) v := by
  funext i
  cases i <;>
    simp [Weil.UnitarySplitting.FourierCovariance.Construction.fourierPhaseRotation, Weil.UnitarySplitting.FourierCovariance.Construction.phaseMomentum, Weil.UnitarySplitting.FourierCovariance.Construction.phasePosition,
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction, Weil.Local.Generators.Construction.weylSymplectic, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

include hc hu in
theorem exists_weyl_lift [CompleteSpace k]
    (hk : ¬ DiscreteTopology k) (hn : ∃ t : k, ψ t ≠ 1) :
    ∃ w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ, Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ w = Weil.Local.Generators.Construction.weylSymplectic k N := by
  obtain ⟨U, hunit, hcov⟩ := Weil.UnitarySplitting.FourierPairing.Construction.exists_ultra_unitary_fourier (d := N) hk ψ hc hu hn
  refine ⟨⟨(Weil.Local.Generators.Construction.weylSymplectic k N, U), ⟨hunit, ?_⟩⟩, rfl⟩
  intro v f h
  have heq : Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔ h = Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f := by
    change h.val = (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f).val ↔ h = Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f
    exact Subtype.ext_iff.symm
  rw [heq]
  have heq' : Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.weylSymplectic k N) v) (U f) (U h) ↔
      U h = Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.weylSymplectic k N) v) (U f) := by
    change (U h).val = (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc
      (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.weylSymplectic k N) v) (U f)).val ↔ _
    exact Subtype.ext_iff.symm
  rw [heq', ← phaseRotation_eq_weyl, ← hcov]
  exact U.injective.eq_iff.symm

def upperLift (w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N) : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ :=
  w⁻¹ * quadraticLift ψ hc hu ⟨-B.val, B.property.neg⟩ * w

omit [SecondCountableTopology k] in
theorem upperLift_projection (w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hw : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ w = Weil.Local.Generators.Construction.weylSymplectic k N)
    (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix k N) :
    Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (upperLift ψ hc hu w B) =
      Weil.AdelicSplitting.SymplecticGeneration.upper B.val B.property := by
  rw [upperLift, map_mul, map_mul, map_inv, hw, quadraticLift_projection]
  change Weil.AdelicSplitting.SymplecticGeneration.weyl⁻¹ *
    Weil.AdelicSplitting.SymplecticGeneration.lower (-B.val) B.property.neg *
      Weil.AdelicSplitting.SymplecticGeneration.weyl = _
  rw [Weil.AdelicSplitting.SymplecticGeneration.lower_conjugation]
  simp only [neg_neg]
  group

def coordinateLift (w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (g : BigCellOne.BigCell (k := k) (N := N)) :
    Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ :=
  quadraticLift ψ hc hu ⟨BigCellOne.lowerPart g, (BigCellOne.parameters_symmetric g).1⟩ *
    Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (BigCellOne.linearPart g) *
      upperLift ψ hc hu w ⟨BigCellOne.upperPart g, (BigCellOne.parameters_symmetric g).2⟩

theorem coordinateLift_projection (w : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hw : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ w = Weil.Local.Generators.Construction.weylSymplectic k N)
    (g : BigCellOne.BigCell (k := k) (N := N)) :
    Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (coordinateLift ψ hc hu w g) = g.val := by
  rw [coordinateLift, map_mul, map_mul, upperLift_projection ψ hc hu w hw,
    quadraticLift_projection]
  exact (BigCellOne.factorization g).symm

end

end OAI.RepresentationTheory.Theta.Adelic.LocalGenerators
