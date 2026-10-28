import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentObjectIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

/-! # Ordinary Datum -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary

noncomputable section

/-!
# Canonical ordinary descent data from a specified geometric line recovery
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Y.Modules)

/-- The pseudofunctor comparison for a specified composite is the standard geometric pullback path. -/
theorem fiberIsoTo_eq {T : Scheme.{u}} (a : T ⟶ X) (b : T ⟶ Y) (h : a ≫ f = b) :
    PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks f P a b h =
      (Scheme.Modules.pullbackComp a f ≪≫ Scheme.Modules.pullbackCongr h).app P := by
  subst b
  apply Iso.ext
  rfl

/-- The ordinary datum obtained by pulling back the specified quotient module. -/
def baseDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f) :=
  Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks) (f := fun (_ : PUnit.{1}) => f) P

/-- The canonical datum uses exactly the standard geometric kernel-pair gluing. -/
theorem baseDatum_gluing : (Geometric.CechInvariant.relationGluing f (baseDatum f P)).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f) pullback.condition).hom.app P := by
  change (PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks f P (pullback.fst f f)
      (pullback.snd f f ≫ f) pullback.condition).hom ≫
    (PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks f P (pullback.snd f f)
      (pullback.snd f f ≫ f) rfl).inv = _
  rw [fiberIsoTo_eq, fiberIsoTo_eq]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
  rfl

variable (M : X.Modules) (e : (Scheme.Modules.pullback f).obj P ≅ M)

/-- A specified recovery transports the canonical ordinary datum onto the actual source module. -/
def ofRecovery : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f) :=
  Ordinary.DescentObjectIso.ofIso Geometric.KernelLinearization.modulePullbacks f (baseDatum f P) M e.symm

/-- The given recovery automatically respects the resulting full geometric descent datum. -/
theorem recovery_compatible :
    (Scheme.Modules.pullback (pullback.fst f f)).map e.hom ≫ (Geometric.CechInvariant.relationGluing f (ofRecovery f P M e)).hom =
      (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f) pullback.condition).hom.app P ≫
        (Scheme.Modules.pullback (pullback.snd f f)).map e.hom := by
  change (Scheme.Modules.pullback (pullback.fst f f)).map e.hom ≫
      (Scheme.Modules.pullback (pullback.fst f f)).map e.inv ≫
      (Geometric.CechInvariant.relationGluing f (baseDatum f P)).hom ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map e.hom = _
  rw [← Category.assoc, ← Functor.map_comp, e.hom_inv_id,
    (Scheme.Modules.pullback (pullback.fst f f)).map_id, Category.id_comp, baseDatum_gluing]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary
