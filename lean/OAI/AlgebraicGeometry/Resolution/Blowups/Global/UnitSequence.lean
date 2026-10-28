import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Sequence
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Dimension

/-! # Unit Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Finite actual global smooth blowup sequences with varying positive controls and unit final ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive UnitSequence.Construction.SmoothGlobalUnitSequence : (X : Scheme) → (X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → X.IdealSheafData → Type 1
  | terminal {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] : SmoothGlobalUnitSequence X f ⊤
  | blowup {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
      (I : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b)
      (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
      (tail : SmoothGlobalUnitSequence (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b)) : SmoothGlobalUnitSequence X f J

def MonomialSequence.Construction.SmoothFixedControlSequence.attachUnit {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J)
    (rest : UnitSequence.Construction.SmoothGlobalUnitSequence T.endpoint (T.toBase ≫ f) T.terminalIdeal) :
    UnitSequence.Construction.SmoothGlobalUnitSequence X f J := by
  induction T with
  | terminal ht => simpa only [MonomialSequence.Construction.SmoothFixedControlSequence.endpoint, MonomialSequence.Construction.SmoothFixedControlSequence.toBase, MonomialSequence.Construction.SmoothFixedControlSequence.terminalIdeal, Category.id_comp] using rest
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      apply UnitSequence.Construction.SmoothGlobalUnitSequence.blowup I hI b hb hp hs hbl
      apply ih
      simpa only [MonomialSequence.Construction.SmoothFixedControlSequence.endpoint, MonomialSequence.Construction.SmoothFixedControlSequence.toBase, MonomialSequence.Construction.SmoothFixedControlSequence.terminalIdeal, Category.assoc] using rest

theorem MonomialSequence.Construction.SmoothFixedControlSequence.endpoint_dimension_le {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {J : X.IdealSheafData} (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J)
    (d : ℕ) (hd : topologicalKrullDim X ≤ d) : topologicalKrullDim T.endpoint ≤ d := by
  revert hd
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs K ht => intro _ hd; exact hd
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      intro hg hd
      let : Smooth g := hg
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      exact ih (GlobalBlowup.Dimension.Construction.globalBlowup_dimension_le g I hI d hd)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
