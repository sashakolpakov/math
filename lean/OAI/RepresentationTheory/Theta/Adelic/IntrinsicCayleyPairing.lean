import OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates
import OAI.RepresentationTheory.Theta.Adelic.UltraCayleyNormalization

/-! # Intrinsic Cayley Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicCayleyPairing.Intrinsic

noncomputable section

/-! Compare the actual UnitarySplitting canonical Cayley operator with the corrected
native weak integral when its coordinate action is the specified matrix. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

variable {k E : Type} [NormedField k] [NormedField E] [Algebra k E] {n m : ℕ}
variable (σ : E ≃ₐ[k] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
variable (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)

theorem frameAction_eq_native (α : Weil.UnitarySplitting.FrameTransport.Construction.StandardSymplectic k (n * m)) (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k (n * m))
    (h : CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c α) = g)
    (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m)) : α.val x = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction g x := by
  rw [← h, CircleCoordinates.coordinateSymplectic_apply, Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic_coordinates, c.coordinates.apply_symm_apply]

variable [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
variable [IsUltrametricDist k] [ProperSpace k] [NonarchimedeanAddGroup k]
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
variable (hn : ∃ x : k, ψ x ≠ 1)

theorem ultraCayley_pairing_native
    (α : Weil.UnitarySplitting.FrameTransport.Construction.StandardSymplectic k (n * m))
    (D : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m) ≃ₗ[k] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m)) (hD : ∀ x, D x = α.val x - x)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k (n * m)) (hg : (g.val - 1).det ≠ 0)
    (hα : ∀ x, α.val x = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction g x) :
    let ν := Measure.pi (fun _ : Fin (n * m) ⊕ Fin (n * m) => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)
    letI : ν.IsAddHaarMeasure := by
      let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
        Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ
          (Weil.AdelicSplitting.NonarchimedeanReference.LocalAnalysis.nonarchimedean_one_coordinate_normalization ψ hu hc hn).1
      infer_instance
    ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
      (∫ x, ((Weil.UnitarySplitting.CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hk ψ hc hu hn ν α D hD).val.2 f).val x * conj (h.val x)
        ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
        Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ g f.val h.val := by
  have heα : α = Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (n * m) g := by
    apply Subtype.ext
    exact LinearEquiv.ext hα
  subst α
  have heD : D = Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k (n * m) g hg := by
    apply LinearEquiv.ext
    intro x
    exact (hD x).trans (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply k (n * m) g hg x).symm
  subst D
  dsimp only
  exact (UltraCayleyNormalization.ultra_cayley_radius_and_pairing σ H K c hk ψ hc hu hn g hg).2

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicCayleyPairing.Intrinsic
