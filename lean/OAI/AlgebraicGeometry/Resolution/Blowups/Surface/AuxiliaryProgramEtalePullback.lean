import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogProgramEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.AuxiliaryProgram

/-! # Auxiliary Program Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! Surface auxiliary programs retain their full named input under étale pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem AuxiliaryProgram.Construction.SurfaceAuxiliaryProgram.exists_etale_pullback
    {n ℓ : ℕ} {β : Type} [Fintype β] [DecidableEq β] {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData} {j : β}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g K}
    (H : AuxiliaryProgram.Construction.SurfaceAuxiliaryProgram n ℓ β X f J D j Y g K P)
    (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V] (hdV : topologicalKrullDim V ≤ 2)
    (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData) (E : β → V.IdealSheafData)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hL : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal L (E j) (n + 1)) W k M)
      (r : W ⟶ Y), AuxiliaryProgram.Construction.SurfaceAuxiliaryProgram n ℓ β V h L E j W k M Q ∧ P.EtaleComparison Q q r := by
  apply LogarithmicProgram.Construction.SurfaceLogarithmicProgram.exists_etale_pullback H V hdV h
    (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal L (E j) (n + 1)) (fun l : {l : β // l ≠ j} => E l.val) q hstructure
  · rw [GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_comap, hL, hD]
  · intro l
    exact hD l.val

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
