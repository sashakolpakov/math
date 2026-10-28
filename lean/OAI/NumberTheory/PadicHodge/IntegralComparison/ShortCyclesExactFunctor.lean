import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.CyclesExactFunctor

/-! # Short Cycles Exact Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ShortCyclesExactFunctor

noncomputable section

/-! Canonical transport of cycles and their short exact sequences along exact functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {T : ShortComplex C} {U : ShortComplex D} (φ : T.map F ⟶ U)

def cycleMap : F.obj T.cycles ⟶ U.cycles :=
  (T.mapCyclesIso F).inv ≫ ShortComplex.cyclesMap φ

theorem cycleMap_i : cycleMap F φ ≫ U.iCycles = F.map T.iCycles ≫ φ.τ₂ := by
  have h : (T.mapCyclesIso F).inv ≫ (T.map F).iCycles = F.map T.iCycles :=
    (congrArg (fun a => (T.mapCyclesIso F).inv ≫ a) (T.mapCyclesIso_hom_iCycles F)).symm.trans
      (Iso.inv_hom_id_assoc _ _)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (T.mapCyclesIso F).inv ≫ a) (ShortComplex.cyclesMap_i φ)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ φ.τ₂) h)))

theorem toCycles : F.map T.toCycles ≫ cycleMap F φ = φ.τ₁ ≫ U.toCycles := by
  apply (cancel_mono U.iCycles).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => F.map T.toCycles ≫ h) (cycleMap_i F φ)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ φ.τ₂) (F.map_comp T.toCycles T.iCycles).symm).trans
          ((congrArg (fun h => F.map h ≫ φ.τ₂) T.toCycles_i).trans
            (φ.comm₁₂.symm.trans
              ((congrArg (fun h => φ.τ₁ ≫ h) U.toCycles_i.symm).trans
                (Category.assoc _ _ _).symm))))))

variable {A : C} {B : D} (a : A ⟶ T.X₁) (b : B ⟶ U.X₁)
  (ha : a ≫ T.toCycles = 0) (hb : b ≫ U.toCycles = 0)
  (g : F.obj A ⟶ B) (hg : g ≫ b = F.map a ≫ φ.τ₁)

def sequenceMap : (ShortComplex.mk a T.toCycles ha).map F ⟶ ShortComplex.mk b U.toCycles hb where
  τ₁ := g
  τ₂ := φ.τ₁
  τ₃ := cycleMap F φ
  comm₁₂ := hg
  comm₂₃ := (ShortCyclesExactFunctor.toCycles F φ).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ShortCyclesExactFunctor
