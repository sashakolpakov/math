import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.FiberTransport

/-! # Recovered Fibers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.RecoveredFibers

noncomputable section

/-!
# Explicit geometric recovery of the full ordinary descent transport
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (D : KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)) (P : Y.Modules)
  (e : (Scheme.Modules.pullback f).obj P ≅ D.obj PUnit.unit)
  (he : (Scheme.Modules.pullback (pullback.fst f f)).map e.hom ≫ (CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f) pullback.condition).hom.app P ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map e.hom)

include he in
/-- The geometric recovery equation is precisely the kernel-pair compatibility for the actual pullback pseudofunctor. -/
theorem kernelPair_compatible :
    (Scheme.Modules.pullback (pullback.fst f f)).map e.hom ≫
      D.hom (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (pullback.fst f f) (pullback.snd f f) pullback.condition rfl =
    (Pseudofunctor.DescentData.ofObj (F := KernelLinearization.modulePullbacks) (f := fun (_ : PUnit.{1}) => f) P).hom
        (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (pullback.fst f f) (pullback.snd f f) pullback.condition rfl ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map e.hom := by
  change (Scheme.Modules.pullback (pullback.fst f f)).map e.hom ≫ (CechInvariant.relationGluing f D).hom =
    (CechInvariant.relationGluing f (Recovered.OrdinaryDatum.Ordinary.baseDatum f P)).hom ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map e.hom
  rw [Recovered.OrdinaryDatum.Ordinary.baseDatum_gluing]
  exact he

/-- The canonical recovered fiber is written using the actual geometric composition and equality comparisons. -/
def recoveryIso {T : Scheme.{u}} (x : T ⟶ X) (q : T ⟶ Y) (hx : x ≫ f = q) :
    (Scheme.Modules.pullback q).obj P ≅ (Scheme.Modules.pullback x).obj (D.obj PUnit.unit) :=
  (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).symm.app P ≪≫
    (Scheme.Modules.pullback x).mapIso e

/-- The native descent comparison equals the explicit geometric recovered-fiber isomorphism. -/
theorem recoveryIso_eq {T : Scheme.{u}} (x : T ⟶ X) (q : T ⟶ Y) (hx : x ≫ f = q) :
    Recovered.FiberTransport.recoveryIso KernelLinearization.modulePullbacks f D P e x q hx = recoveryIso f D P e x q hx := by
  unfold Recovered.FiberTransport.recoveryIso
  rw [Recovered.OrdinaryDatum.Ordinary.fiberIsoTo_eq]
  rfl

include he in
/-- Every actual test fiber is recovered compatibly with the full supplied geometric descent datum. -/
theorem recovery_hom {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (recoveryIso f D P e x q hx).hom ≫ D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      (recoveryIso f D P e y q hy).hom := by
  have h := Recovered.FiberTransport.recovery_hom KernelLinearization.modulePullbacks f D P e
    (kernelPair_compatible f D P e he) q x y hx hy
  rw [recoveryIso_eq, recoveryIso_eq] at h
  exact h

include he in
/-- The original transport between two test fibers is the change between their actual geometric recoveries. -/
theorem transport_eq {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      (recoveryIso f D P e x q hx).inv ≫ (recoveryIso f D P e y q hy).hom := by
  have h := Recovered.FiberTransport.transport_eq KernelLinearization.modulePullbacks f D P e
    (kernelPair_compatible f D P e he) q x y hx hy
  rw [recoveryIso_eq, recoveryIso_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.RecoveredFibers
