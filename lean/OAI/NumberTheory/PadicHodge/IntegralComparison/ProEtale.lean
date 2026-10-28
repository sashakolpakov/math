import Mathlib

/-! # Pro Etale -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale

noncomputable section

/-!
# IntegralComparison: transport of the pro-étale site by scheme isomorphisms

An isomorphism of base schemes acts on the actual pro-étale site by
postcomposing the structure morphism of each object. The underlying
schemes and covering morphisms are preserved.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

instance proEtalePrecoverage_baseChange (X : Scheme.{u}) :
    (Scheme.ProEt.precoverage X).IsStableUnderBaseChange :=
  inferInstanceAs
    (Precoverage.IsStableUnderBaseChange (Scheme.proetalePrecoverage.comap
      (Scheme.ProEt.forget X ⋙ Over.forget X)))

/-- Transport the small pro-étale site along an isomorphism of schemes. -/
def proEtaleCongr (e : X ≅ Y) : X.ProEt ≌ Y.ProEt :=
  MorphismProperty.Comma.mapRightIso
    (P := @WeaklyEtale) (Q := ⊤) (W := ⊤) (𝟭 Scheme)
    (Discrete.natIso (fun _ => e))

@[simp]
lemma proEtaleCongr_obj_left (e : X ≅ Y) (U : X.ProEt) :
    ((proEtaleCongr e).functor.obj U).left = U.left := rfl

@[simp]
lemma proEtaleCongr_obj_hom (e : X ≅ Y) (U : X.ProEt) :
    ((proEtaleCongr e).functor.obj U).hom = U.hom ≫ e.hom := rfl

lemma proEtaleCongr_forget (e : X ≅ Y) :
    (proEtaleCongr e).functor ⋙ Scheme.ProEt.forget Y ⋙ Over.forget Y =
      Scheme.ProEt.forget X ⋙ Over.forget X := rfl

lemma proEtaleCongr_comap_precoverage (e : X ≅ Y) :
    (Scheme.ProEt.precoverage Y).comap (proEtaleCongr e).functor =
      Scheme.ProEt.precoverage X := by
  change (Scheme.proetalePrecoverage.comap
    (Scheme.ProEt.forget Y ⋙ Over.forget Y)).comap (proEtaleCongr e).functor = _
  rw [← Precoverage.comap_comp, proEtaleCongr_forget]
  rfl

instance proEtaleCongr_continuous (e : X ≅ Y) :
    (proEtaleCongr e).functor.IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
    (proEtaleCongr e).functor (Scheme.ProEt.precoverage X) (Scheme.ProEt.precoverage Y)
  exact (proEtaleCongr_comap_precoverage e).ge

instance proEtaleCongr_inverse_continuous (e : X ≅ Y) :
    (proEtaleCongr e).inverse.IsContinuous
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  inferInstanceAs ((proEtaleCongr e.symm).functor.IsContinuous
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))

variable (A : Type*) [Category A]

/-- A scheme isomorphism induces an equivalence of its pro-étale sheaf
categories, by restriction along the equivalence of sites. -/
def proEtaleSheafCongr (e : X ≅ Y) :
    Sheaf (Scheme.ProEt.topology X) A ≌ Sheaf (Scheme.ProEt.topology Y) A where
  functor := (proEtaleCongr e).inverse.sheafPushforwardContinuous A
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  inverse := (proEtaleCongr e).functor.sheafPushforwardContinuous A
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
  unitIso := NatIso.ofComponents (fun F =>
    ObjectProperty.isoMk _ (isoWhiskerRight (proEtaleCongr e).op.unitIso F.obj))
    (fun {F G} α => by
      ext U
      exact (α.hom.naturality ((proEtaleCongr e).op.unitIso.hom.app U)).symm)
  counitIso := NatIso.ofComponents (fun F =>
    ObjectProperty.isoMk _ (isoWhiskerRight (proEtaleCongr e).op.counitIso F.obj))
    (fun {F G} α => by
      ext U
      exact (α.hom.naturality ((proEtaleCongr e).op.counitIso.hom.app U)).symm)
  functor_unitIso_comp F := by
    ext U
    change F.obj.map ((proEtaleCongr e).op.unitIso.hom.app
        ((proEtaleCongr e).op.inverse.obj U)) ≫
      F.obj.map ((proEtaleCongr e).op.inverse.map
        ((proEtaleCongr e).op.counitIso.hom.app U)) = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, Equivalence.unit_inverse_comp]
    exact F.obj.map_id _

instance proEtaleSheafCongr_additive [Preadditive A] (e : X ≅ Y) :
    (proEtaleSheafCongr A e).functor.Additive where
  map_add := by intros; rfl

instance proEtaleSheafCongr_linear (R : Type*) [Ring R] [Preadditive A] [Linear R A]
    (e : X ≅ Y) : (proEtaleSheafCongr A e).functor.Linear R where
  map_smul := by intros; rfl

/-- Constant sheaves commute with transport of the base scheme. This
isomorphism follows from their global-sections adjunction. -/
def proEtaleSheafCongr_constant (e : X ≅ Y)
    [HasWeakSheafify (Scheme.ProEt.topology X) A]
    [HasWeakSheafify (Scheme.ProEt.topology Y) A] :
    constantSheaf (Scheme.ProEt.topology X) A ⋙ (proEtaleSheafCongr A e).functor ≅
      constantSheaf (Scheme.ProEt.topology Y) A :=
  ((constantSheafAdj (Scheme.ProEt.topology X) A
      (terminalIsTerminal : IsTerminal (⊤_ X.ProEt))).comp
    (proEtaleSheafCongr A e).toAdjunction).leftAdjointUniq
      (constantSheafAdj (Scheme.ProEt.topology Y) A
        (terminalIsTerminal.isTerminalObj (proEtaleCongr e).functor (⊤_ X.ProEt)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale
