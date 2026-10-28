import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections
import Mathlib.CategoryTheory.Endomorphism

/-! # Unit End Pullback -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UnitEndPullback.Construction

noncomputable section

/-! Pullback of endomorphisms of the structure sheaf is pullback of their scalar functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem structureSheafEnd_isIso_iff (X : Scheme.{u}) (q : End (LineBundle.Construction.structureSheafModule X)) :
    IsIso q ↔ IsUnit (ModuleSections.Construction.structureSheafEndRingEquiv X q) := by
  constructor
  · intro hq
    exact ((isUnit_iff_isIso q).mpr hq).map (ModuleSections.Construction.structureSheafEndRingEquiv X)
  · intro hq
    apply (isUnit_iff_isIso q).mp
    simpa only [RingEquiv.symm_apply_apply] using hq.map (ModuleSections.Construction.structureSheafEndRingEquiv X).symm

def pullbackUnitScalar {X Y : Scheme.{u}} (f : X ⟶ Y) (q : End (LineBundle.Construction.structureSheafModule Y)) :
    End (LineBundle.Construction.structureSheafModule X) :=
  (ModuleSections.Construction.structureSheafEndRingEquiv X).symm (f.appTop (ModuleSections.Construction.structureSheafEndRingEquiv Y q))

theorem structureSheafToPushforward_end {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : End (LineBundle.Construction.structureSheafModule Y)) :
    q ≫ TensorUnit.Construction.structureSheafToPushforward f =
      TensorUnit.Construction.structureSheafToPushforward f ≫ (Scheme.Modules.pushforward f).map (pullbackUnitScalar f q) := by
  apply (ModuleSections.Construction.structureSheafHomEquiv ((Scheme.Modules.pushforward f).obj (LineBundle.Construction.structureSheafModule X))).injective
  change f.appTop (ModuleSections.Construction.structureSheafEndRingEquiv Y q) =
    (pullbackUnitScalar f q).app ⊤ (f.appTop (1 : Γ(Y, ⊤)))
  rw [map_one]
  exact ((ModuleSections.Construction.structureSheafEndRingEquiv X).apply_symm_apply (f.appTop (ModuleSections.Construction.structureSheafEndRingEquiv Y q))).symm

theorem pullbackUnitEnd_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : End (LineBundle.Construction.structureSheafModule Y)) :
    (Scheme.Modules.pullback f).map q ≫ (LineBundle.Construction.pullbackStructureSheafIso f).hom =
      (LineBundle.Construction.pullbackStructureSheafIso f).hom ≫ pullbackUnitScalar f q := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have he : adj.homEquiv (LineBundle.Construction.structureSheafModule Y) (LineBundle.Construction.structureSheafModule X)
      (LineBundle.Construction.pullbackStructureSheafIso f).hom = TensorUnit.Construction.structureSheafToPushforward f :=
    (adj.homEquiv_unit _ _ _).trans (TensorUnit.Construction.pullbackStructureSheafIso_unit f)
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, he]
  exact structureSheafToPushforward_end f q

theorem isIso_pullback_unitEnd_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : End (LineBundle.Construction.structureSheafModule Y)) :
    IsIso ((Scheme.Modules.pullback f).map q) ↔
      IsUnit (f.appTop (ModuleSections.Construction.structureSheafEndRingEquiv Y q)) := by
  have hscalar : IsIso (pullbackUnitScalar f q) ↔
      IsUnit (f.appTop (ModuleSections.Construction.structureSheafEndRingEquiv Y q)) := by
    rw [structureSheafEnd_isIso_iff, pullbackUnitScalar, RingEquiv.apply_symm_apply]
  rw [← hscalar]
  constructor
  · intro hq
    have hi : IsIso ((LineBundle.Construction.pullbackStructureSheafIso f).hom ≫ pullbackUnitScalar f q) := by
      rw [← pullbackUnitEnd_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (LineBundle.Construction.pullbackStructureSheafIso f).hom _
  · intro hq
    have hi : IsIso ((Scheme.Modules.pullback f).map q ≫ (LineBundle.Construction.pullbackStructureSheafIso f).hom) := by
      rw [pullbackUnitEnd_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (LineBundle.Construction.pullbackStructureSheafIso f).hom

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UnitEndPullback.Construction
