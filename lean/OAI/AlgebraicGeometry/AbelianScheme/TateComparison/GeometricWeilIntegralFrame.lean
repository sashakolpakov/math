import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricWeilBalance
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearDualTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SelfDualBlockLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteChosenFlags
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface

/-! # Geometric Weil Integral Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual integral Tate lattice in a compatible frame consists
of the chosen source lattices and their Weil dual opposite lattices. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hf in
theorem Data.SphericalPELAlbaneseData.geometricWeilSource_opposite (v : Fin s) :
    (D.framedFiberSourceLattice b x frame (v, true)).val =
      (D.framedOppositePairing (D.fiberFamily b x) _ frame
        (D.geometricRationalWeilPairing hg hgeometry b x) v).dualSubmodule
          (D.framedFiberSourceLattice b x frame (v, false)).val := by
  have hd := BilinearDualTransport.bilinearSelfDual_congr (D.geometricRationalWeilPairing hg hgeometry b x) frame _
    (D.geometricRationalWeilPairing_self_dual hg hgeometry b x)
  change (LinearMap.BilinForm.congr frame (D.geometricRationalWeilPairing hg hgeometry b x)).dualSubmodule
    (Rational.framedIntegralTateImage frame) = Rational.framedIntegralTateImage frame at hd
  rw [D.framedIntegralTateImage_eq_pi hg _ (D.fiberFamily b x) frame hf] at hd
  exact SelfDualBlockLattices.oppositeBlockLattice_of_self_dual
    (LinearMap.BilinForm.congr frame (D.geometricRationalWeilPairing hg hgeometry b x))
    Data.SphericalPELAlbaneseData.oppositeBlock Data.SphericalPELAlbaneseData.oppositeBlock_involutive.injective
    (D.geometricWeilFrame_orthogonal hg hgeometry b x frame hf)
    (D.framedSourceLattice _ (D.fiberFamily b x) frame) hd (v, false)

include hf in
theorem Data.SphericalPELAlbaneseData.geometricWeil_isIntegralSplitFrame :
    D.IsIntegralSplitFrame b x frame
      (D.framedOppositePairing (D.fiberFamily b x) _ frame
        (D.geometricRationalWeilPairing hg hgeometry b x))
      (fun v => D.framedFiberSourceLattice b x frame (v, false)) := by
  refine ⟨hf, ?_⟩
  rw [D.framedIntegralTateImage_eq_pi hg _ (D.fiberFamily b x) frame hf]
  congr 1
  funext v
  obtain ⟨v, side⟩ := v
  cases side
  · rfl
  · exact D.geometricWeilSource_opposite hg hgeometry b x frame hf v

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
