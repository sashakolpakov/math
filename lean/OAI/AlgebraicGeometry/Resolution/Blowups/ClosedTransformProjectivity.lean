import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceHypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedTransformMap

/-! # Closed Transform Projectivity -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Every actual global control sequence induces a proper map of its controlled closed subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.transformIdeal_total_le (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J)
    (H : X.IdealSheafData) (c : ℕ) : H.comap T.toBase ≤ T.transformIdeal H c := by
  revert H
  induction T with
  | @terminal Y g hs K ht =>
      intro H
      change H.comap (𝟙 Y) ≤ H
      rw [Scheme.IdealSheafData.comap_id]
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      intro H
      change H.comap (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≤
        tail.transformIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI c) c
      rw [Scheme.IdealSheafData.comap_comp]
      exact (Scheme.IdealSheafData.comap_mono tail.toBase
        (GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I H c (GlobalBlowup.Data.Construction.globalBlowupToBase I hI))).trans
          (ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI c))

def Global.MonomialSequence.Construction.SmoothFixedControlSequence.transformedSubschemeToBase (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J)
    (H : X.IdealSheafData) (c : ℕ) : (T.transformIdeal H c).subscheme ⟶ H.subscheme :=
  ClosedTransformMap.Construction.closedTransformMap T.toBase H (T.transformIdeal H c) (T.transformIdeal_total_le H c)

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.transformedSubschemeToBase_over (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J)
    (H : X.IdealSheafData) (c : ℕ) :
    T.transformedSubschemeToBase H c ≫ H.subschemeι = (T.transformIdeal H c).subschemeι ≫ T.toBase :=
  ClosedTransformMap.Construction.closedTransformMap_over T.toBase H (T.transformIdeal H c) (T.transformIdeal_total_le H c)

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.transformedSubschemeToBase_isProper (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J)
    (H : X.IdealSheafData) (c : ℕ) : IsProper (T.transformedSubschemeToBase H c) :=
  ClosedTransformMap.Construction.closedTransformMap_isProper T.toBase H (T.transformIdeal H c) (T.transformIdeal_total_le H c)

end

/-! Native projective presentations of actual closed transforms on global blowup endpoints. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def ClosedTransformProjectivity.Construction.closedSubschemeProjectivePresentation
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) (H : X.IdealSheafData) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation H.subscheme (H.subschemeι ≫ f) := by
  let : IsClosedImmersion P.embedding := P.closedImmersion
  refine ⟨P.ambientDimension, H.subschemeι ≫ P.embedding, inferInstance, ?_⟩
  rw [Category.assoc, P.over_base]

def Global.MonomialSequence.Construction.SmoothFixedControlSequence.transformedSubschemeProjectivePresentation
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (H : X.IdealSheafData) (c : ℕ) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (T.transformIdeal H c).subscheme
      ((T.transformIdeal H c).subschemeι ≫ (T.toBase ≫ f)) :=
  ClosedTransformProjectivity.Construction.closedSubschemeProjectivePresentation (T.endpointProjectivePresentation P) (T.transformIdeal H c)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
