import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UnitSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback

/-! # Global Unit Sequence Geometry -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Proper birational projective endpoints and exact total transforms for global unit sequences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def UnitSequence.Construction.SmoothGlobalUnitSequence.endpoint {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) : Scheme :=
  match T with
  | @UnitSequence.Construction.SmoothGlobalUnitSequence.terminal Y _ _ => Y
  | @UnitSequence.Construction.SmoothGlobalUnitSequence.blowup _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.endpoint

def UnitSequence.Construction.SmoothGlobalUnitSequence.toBase {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) : T.endpoint ⟶ X :=
  match T with
  | @UnitSequence.Construction.SmoothGlobalUnitSequence.terminal Y _ _ => 𝟙 Y
  | @UnitSequence.Construction.SmoothGlobalUnitSequence.blowup _ _ _ _ _ I hI _ _ _ _ _ tail => tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI

def UnitSequence.Construction.SmoothGlobalUnitSequence.exceptionalProduct {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) : T.endpoint.IdealSheafData :=
  match T with
  | @UnitSequence.Construction.SmoothGlobalUnitSequence.terminal _ _ _ => ⊤
  | @UnitSequence.Construction.SmoothGlobalUnitSequence.blowup _ _ _ _ _ I hI b _ _ _ _ tail =>
      (I.comap (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b * tail.exceptionalProduct

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}

instance UnitSequence.Construction.SmoothGlobalUnitSequence.toBase_isProper (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) : IsProper T.toBase := by
  induction T with
  | @terminal Y g hs => exact inferInstanceAs (IsProper (𝟙 Y))
  | blowup I hI b hb hp hs hbl tail ih =>
      let : IsProper tail.toBase := ih
      exact inferInstanceAs (IsProper (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI))

instance UnitSequence.Construction.SmoothGlobalUnitSequence.endpoint_structure_smooth (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) : Smooth (T.toBase ≫ f) := by
  induction T with
  | @terminal Y g hs => simpa only [UnitSequence.Construction.SmoothGlobalUnitSequence.endpoint, UnitSequence.Construction.SmoothGlobalUnitSequence.toBase, Category.id_comp] using hs
  | blowup I hI b hb hp hs hbl tail ih =>
      simpa only [UnitSequence.Construction.SmoothGlobalUnitSequence.endpoint, UnitSequence.Construction.SmoothGlobalUnitSequence.toBase, Category.assoc] using ih

theorem UnitSequence.Construction.SmoothGlobalUnitSequence.endpoint_integral (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) [IsIntegral X] :
    IsIntegral T.endpoint := by
  revert ‹IsIntegral X›
  induction T with
  | terminal => intro h; exact h
  | blowup I hI b hb hp hs hbl tail ih => intro _; exact ih

theorem UnitSequence.Construction.SmoothGlobalUnitSequence.toBase_partialIso (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) :
    ∃ e : T.endpoint.PartialIso X, e.source.ι ≫ T.toBase = e.iso.hom ≫ e.target.ι := by
  induction T with
  | @terminal Y g hs =>
      refine ⟨Scheme.PartialIso.refl Y, ?_⟩
      change (⊤ : Y.Opens).ι ≫ 𝟙 Y = 𝟙 (⊤ : Y.Opens).toScheme ≫ (⊤ : Y.Opens).ι
      simp only [Category.comp_id, Category.id_comp]
  | blowup I hI b hb hp hs hbl tail ih =>
      obtain ⟨e, he⟩ := ih
      obtain ⟨d, hd⟩ := GlobalBlowup.Data.Construction.globalBlowup_partialIso I hI
      exact ⟨e.trans d, Sequence.Construction.compatible_partialIso_comp tail.toBase (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) e he d hd⟩

def UnitSequence.Construction.SmoothGlobalUnitSequence.endpointProjectivePresentation (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) : Foundations.Scheme.SmoothProjective.ProjectivePresentation T.endpoint (T.toBase ≫ f) := by
  induction T with
  | terminal => simpa only [UnitSequence.Construction.SmoothGlobalUnitSequence.endpoint, UnitSequence.Construction.SmoothGlobalUnitSequence.toBase, Category.id_comp] using P
  | blowup I hI b hb hp hs hbl tail ih =>
      have Q := ih (GlobalBlowup.Projectivity.Construction.globalBlowupProjectivePresentation P I hI)
      simpa only [UnitSequence.Construction.SmoothGlobalUnitSequence.endpoint, UnitSequence.Construction.SmoothGlobalUnitSequence.toBase, Category.assoc] using Q

def UnitSequence.Construction.SmoothGlobalUnitSequence.endpointVariety (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) [IsIntegral X]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  ⟨{ carrier := T.endpoint
     structureMap := T.toBase ≫ f
     projective := T.endpointProjectivePresentation P
     smooth := inferInstance }, T.endpoint_integral⟩

theorem UnitSequence.Construction.SmoothGlobalUnitSequence.exceptionalProduct_eq_totalTransform (T : UnitSequence.Construction.SmoothGlobalUnitSequence X f J) :
    T.exceptionalProduct = J.comap T.toBase := by
  induction T with
  | terminal => exact (Scheme.IdealSheafData.comap_id ⊤).symm
  | @blowup Y hY hN g K I hI b hb hp hs hbl tail ih =>
      change (I.comap (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b *
        tail.exceptionalProduct = K.comap (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
      rw [ih, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
        ← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, ← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul,
        GlobalControlled.Factorization.Construction.globalBlowup_controlledIdeal_factorization I K hI b hp]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
