import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback

/-! # Module Descent Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery

noncomputable section

/-! Changing local descent objects to their actual recovered ambient
modules. All recovery maps retain the native pullback composition paths. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-- The existing slice pullback operation is the native pseudofunctor
pullback on both equal endpoint maps. -/
theorem moduleMapPullbackAlong_eq_pullHom {X : Scheme.{u}} {M N : X.Modules}
    {U V : Over X} (a : U ⟶ V)
    (φ : (Scheme.Modules.pullback V.hom).obj M ⟶ (Scheme.Modules.pullback V.hom).obj N) :
    Module.MapSlicePullback.moduleMapPullbackAlong a φ = pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) φ a.left U.hom U.hom a.w a.w := by
  rw [Picard.PoincareBundle.Geometric.PullHom.pullHom_eq]
  simp only [Module.MapSlicePullback.moduleMapPullbackAlong, Module.MapPullbackCongruence.moduleMapPullbackCongr, Module.MapPullbackComposition.moduleMapPullbackComp,
    Iso.homCongr_apply, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    NatTrans.comp_app, Category.assoc]

namespace NativeModuleDescentRecovery

private theorem conjugate_identity {K : Type*} [Category* K] {X Y : K}
    (r : X ≅ Y) (a : Y ⟶ Y) (ha : a = 𝟙 Y) : r.hom ≫ a ≫ r.inv = 𝟙 X := by
  rw [ha, Category.id_comp, r.hom_inv_id]

private theorem conjugate_composition {K : Type*} [Category* K] {X Y Z A B C : K}
    (r : X ≅ A) (s : Y ≅ B) (t : Z ≅ C) (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (hc : a ≫ b = c) :
    (r.hom ≫ a ≫ s.inv) ≫ (s.hom ≫ b ≫ t.inv) = r.hom ≫ c ≫ t.inv := by
  simp only [Category.assoc, s.inv_hom_id_assoc]
  rw [← Category.assoc a, hc]

variable {X : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
  (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData f) (M : ι → X.Modules)
  (r : ∀ i, (Scheme.Modules.pullback (f i)).obj (M i) ≅ D.obj i)

private def recoveryWithIdentity (i : ι) :
    (Scheme.Modules.pullback (f i)).obj (M i) ≅
      (Scheme.Modules.pullback (𝟙 (Y i))).obj (D.obj i) :=
  r i ≪≫ (Scheme.Modules.pullbackId (Y i)).symm.app (D.obj i)

def recoveryAt {T : Scheme.{u}} (q : T ⟶ X) (i : ι) (a : T ⟶ Y i) (ha : a ≫ f i = q) :
    (Scheme.Modules.pullback q).obj (M i) ≅ (Scheme.Modules.pullback a).obj (D.obj i) :=
  Picard.PoincareBundle.PullbackFiberComposition.pullIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks (recoveryWithIdentity D M r i) a q a ha (Category.comp_id a)

theorem recoveryAt_hom_pullback {T U : Scheme.{u}}
    (t : U ⟶ T) (q : T ⟶ X) (q' : U ⟶ X) (hq : t ≫ q = q')
    (i : ι) (a : T ⟶ Y i) (ha : a ≫ f i = q)
    (a' : U ⟶ Y i) (ha' : a' ≫ f i = q') (hat : t ≫ a = a') :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (recoveryAt D M r q i a ha).hom t q' a' hq hat =
      (recoveryAt D M r q' i a' ha').hom := by
  subst a'
  exact pullHom_pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (recoveryWithIdentity D M r i).hom
    a q a t q' (t ≫ a) ha (Category.comp_id a) hq rfl

theorem recoveryAt_inv_pullback {T U : Scheme.{u}}
    (t : U ⟶ T) (q : T ⟶ X) (q' : U ⟶ X) (hq : t ≫ q = q')
    (i : ι) (a : T ⟶ Y i) (ha : a ≫ f i = q)
    (a' : U ⟶ Y i) (ha' : a' ≫ f i = q') (hat : t ≫ a = a') :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (recoveryAt D M r q i a ha).inv t a' q' hat hq =
      (recoveryAt D M r q' i a' ha').inv := by
  subst a'
  exact pullHom_pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (recoveryWithIdentity D M r i).inv
    a a q t (t ≫ a) q' (Category.comp_id a) ha rfl hq

/-- The original descent isomorphism expressed on actual ambient
pullbacks, rather than on independently specified local sheaves. -/
def ambientIso {T : Scheme.{u}} (q : T ⟶ X) (i j : ι)
    (a : T ⟶ Y i) (b : T ⟶ Y j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (Scheme.Modules.pullback q).obj (M i) ≅ (Scheme.Modules.pullback q).obj (M j) :=
  recoveryAt D M r q i a ha ≪≫ D.iso q a b ha hb ≪≫ (recoveryAt D M r q j b hb).symm

theorem ambientIso_self {T : Scheme.{u}} (q : T ⟶ X) (i : ι)
    (a : T ⟶ Y i) (ha : a ≫ f i = q) :
    ambientIso D M r q i i a a ha ha = Iso.refl _ := by
  apply Iso.ext
  exact conjugate_identity (recoveryAt D M r q i a ha) (D.hom q a a ha ha) (D.hom_self q a ha)

theorem ambientIso_comp {T : Scheme.{u}} (q : T ⟶ X) (i j k : ι)
    (a : T ⟶ Y i) (b : T ⟶ Y j) (c : T ⟶ Y k)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    (ambientIso D M r q i j a b ha hb).hom ≫ (ambientIso D M r q j k b c hb hc).hom =
      (ambientIso D M r q i k a c ha hc).hom := by
  exact conjugate_composition (recoveryAt D M r q i a ha) (recoveryAt D M r q j b hb)
    (recoveryAt D M r q k c hc) (D.hom q a b ha hb) (D.hom q b c hb hc)
    (D.hom q a c ha hc) (D.hom_comp q a b c ha hb hc)

theorem ambientIso_pullback {T U : Scheme.{u}}
    (t : U ⟶ T) (q : T ⟶ X) (q' : U ⟶ X) (hq : t ≫ q = q')
    (i j : ι) (a : T ⟶ Y i) (b : T ⟶ Y j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q)
    (a' : U ⟶ Y i) (b' : U ⟶ Y j)
    (ha' : a' ≫ f i = q') (hb' : b' ≫ f j = q') (hat : t ≫ a = a') (hbt : t ≫ b = b') :
    pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (ambientIso D M r q i j a b ha hb).hom t q' q' hq hq =
      (ambientIso D M r q' i j a' b' ha' hb').hom := by
  have h₁ := Picard.PoincareBundle.PullHom.pullHom_comp (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks)
    (recoveryAt D M r q i a ha).hom
    (D.hom q a b ha hb ≫ (recoveryAt D M r q j b hb).inv) t q' a' q' hq hat hq
  have h₂ := Picard.PoincareBundle.PullHom.pullHom_comp (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (D.hom q a b ha hb)
    (recoveryAt D M r q j b hb).inv t a' b' q' hat hbt hq
  have hi := recoveryAt_hom_pullback D M r t q q' hq i a ha a' ha' hat
  have hj := recoveryAt_inv_pullback D M r t q q' hq j b hb b' hb' hbt
  have hd := D.pullHom_hom t q q' hq a b ha hb a' b' hat hbt
  exact h₁.trans (congrArg₂ (fun x y => x ≫ y) hi
    (h₂.trans (congrArg₂ (fun x y => x ≫ y) hd hj)))

end NativeModuleDescentRecovery

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery
