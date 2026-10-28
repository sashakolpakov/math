import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Global Kernel Linearization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization

noncomputable section

/-!
# Transport from a global kernel-action linearization
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (L : F.obj (.mk (op A)))

attribute [local instance] Kernel.Scheme.kernelGroup

/-- An isomorphism over the actual kernel-action scheme, with the unit and action cocycle. -/
structure ActionLinearization where
  actionIso : (F.map (Kernel.ActionMaps.source f).op.toLoc).toFunctor.obj L ≅
    (F.map (Kernel.ActionMaps.action f).op.toLoc).toFunctor.obj L
  unit : pullHom actionIso.hom (Kernel.ActionMaps.unitSection f) (𝟙 A) (𝟙 A)
    (Kernel.ActionMaps.unitSection_source f) (Kernel.ActionMaps.unitSection_action f) = 𝟙 _
  cocycle :
    pullHom actionIso.hom (Kernel.ActionMaps.firstStep f) (Kernel.ActionMaps.tripleSource f) (Kernel.ActionMaps.tripleMiddle f) rfl rfl ≫
      pullHom actionIso.hom (Kernel.ActionMaps.secondStep f) (Kernel.ActionMaps.tripleMiddle f) (Kernel.ActionMaps.tripleTarget f)
        (Kernel.ActionMaps.secondStep_source f) rfl =
    pullHom actionIso.hom (Kernel.ActionMaps.productStep f) (Kernel.ActionMaps.tripleSource f) (Kernel.ActionMaps.tripleTarget f)
      (Kernel.ActionMaps.productStep_source f) (Kernel.ActionMaps.productStep_action f)

variable (D : ActionLinearization f F L)

/-- Restrict the global action isomorphism to a test point and its kernel translate. -/
def transport {T : C} (x y : T ⟶ A) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hk : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y) : Kernel.Linearization.pointObject F L x ⟶ Kernel.Linearization.pointObject F L y :=
  pullHom D.actionIso.hom (lift x k) x y (lift_fst _ _) ((Kernel.ActionMaps.action_pair f x k).trans hk)

/-- The global unit diagram implies identity transport over every test object. -/
theorem transport_unit {T : C} (x : T ⟶ A)
    (hx : x * ((1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f) = x) :
    GlobalKernelLinearization.transport f F L D x x 1 hx = 𝟙 _ := by
  have h0 : pullHom (pullHom D.actionIso.hom (Kernel.ActionMaps.unitSection f) (𝟙 A) (𝟙 A)
      (Kernel.ActionMaps.unitSection_source f) (Kernel.ActionMaps.unitSection_action f)) x x x
      (Category.comp_id x) (Category.comp_id x) = 𝟙 _ := by
    rw [D.unit]
    exact PullHom.pullHom_identity x x (Category.comp_id x)
  have h1 := pullHom_pullHom D.actionIso.hom (Kernel.ActionMaps.unitSection f) (𝟙 A) (𝟙 A) x x x
    (Kernel.ActionMaps.unitSection_source f) (Kernel.ActionMaps.unitSection_action f) (Category.comp_id x) (Category.comp_id x)
  have h2 := PullHom.pullHom_congr D.actionIso.hom (lift x (1 : T ⟶ Kernel.Scheme.kernelObject f))
    (x ≫ Kernel.ActionMaps.unitSection f) (Kernel.ActionMaps.unitSection_point f x).symm x x (lift_fst _ _)
    ((Kernel.ActionMaps.action_pair f x 1).trans hx)
    (by rw [Category.assoc, Kernel.ActionMaps.unitSection_source, Category.comp_id])
    (by rw [Category.assoc, Kernel.ActionMaps.unitSection_action, Category.comp_id])
  exact h2.trans (h1.symm.trans h0)

/-- Base-change compatibility of the test-object transport follows from pullback functoriality. -/
theorem transport_pullback {T T' : C} (g : T' ⟶ T)
    (x y : T ⟶ A) (k : T ⟶ Kernel.Scheme.kernelObject f) (hk : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y)
    (x' y' : T' ⟶ A) (k' : T' ⟶ Kernel.Scheme.kernelObject f)
    (hk' : x' * (k' ≫ Kernel.Scheme.kernelInclusion f) = y')
    (hx : g ≫ x = x') (hy : g ≫ y = y') (hkk : g ≫ k = k') :
    pullHom (GlobalKernelLinearization.transport f F L D x y k hk) g x' y' hx hy =
      GlobalKernelLinearization.transport f F L D x' y' k' hk' := by
  have h1 := pullHom_pullHom D.actionIso.hom (lift x k) x y g x' y'
    (lift_fst _ _) ((Kernel.ActionMaps.action_pair f x k).trans hk) hx hy
  have hp : g ≫ lift x k = lift x' k' := by rw [Kernel.ActionMaps.pair_naturality, hx, hkk]
  have h2 := PullHom.pullHom_congr D.actionIso.hom (g ≫ lift x k) (lift x' k') hp x' y'
    (by rw [Category.assoc, Kernel.ActionMaps.source, lift_fst, hx])
    (by rw [Category.assoc, Kernel.ActionMaps.action_pair, hk, hy])
    (lift_fst _ _) ((Kernel.ActionMaps.action_pair f x' k').trans hk')
  exact h1.trans h2

/-- The global action cocycle gives composition of transport over every test object. -/
theorem transport_mul {T : C} (x y z : T ⟶ A) (k l m : T ⟶ Kernel.Scheme.kernelObject f)
    (hx : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y) (hy : y * (l ≫ Kernel.Scheme.kernelInclusion f) = z)
    (hz : x * (m ≫ Kernel.Scheme.kernelInclusion f) = z) (hm : k * l = m) :
    GlobalKernelLinearization.transport f F L D x y k hx ≫ GlobalKernelLinearization.transport f F L D y z l hy =
      GlobalKernelLinearization.transport f F L D x z m hz := by
  let t : T ⟶ (A ⊗ Kernel.Scheme.kernelObject f) ⊗ Kernel.Scheme.kernelObject f := lift (lift x k) l
  have ha : t ≫ Kernel.ActionMaps.firstStep f = lift x k := Kernel.ActionMaps.triple_firstStep f x k l
  have hb : t ≫ Kernel.ActionMaps.secondStep f = lift y l :=
    (Kernel.ActionMaps.triple_secondStep f x k l).trans (congrArg (fun a => lift a l) hx)
  have hc : t ≫ Kernel.ActionMaps.productStep f = lift x m :=
    (Kernel.ActionMaps.triple_productStep f x k l).trans (congrArg (lift x) hm)
  have hs : t ≫ Kernel.ActionMaps.tripleSource f = x :=
    (Category.assoc t (Kernel.ActionMaps.firstStep f) (Kernel.ActionMaps.source f)).symm.trans
      ((congrArg (fun a => a ≫ Kernel.ActionMaps.source f) ha).trans (lift_fst x k))
  have hmid : t ≫ Kernel.ActionMaps.tripleMiddle f = y :=
    (Category.assoc t (Kernel.ActionMaps.firstStep f) (Kernel.ActionMaps.action f)).symm.trans
      ((congrArg (fun a => a ≫ Kernel.ActionMaps.action f) ha).trans ((Kernel.ActionMaps.action_pair f x k).trans hx))
  have ht : t ≫ Kernel.ActionMaps.tripleTarget f = z :=
    (Category.assoc t (Kernel.ActionMaps.secondStep f) (Kernel.ActionMaps.action f)).symm.trans
      ((congrArg (fun a => a ≫ Kernel.ActionMaps.action f) hb).trans ((Kernel.ActionMaps.action_pair f y l).trans hy))
  have H := congrArg (fun φ : Kernel.Linearization.pointObject F L (Kernel.ActionMaps.tripleSource f) ⟶
      Kernel.Linearization.pointObject F L (Kernel.ActionMaps.tripleTarget f) => pullHom φ t x z hs ht) D.cocycle
  rw [PullHom.pullHom_comp _ _ t x y z hs hmid ht] at H
  simpa only [GlobalKernelLinearization.transport, pullHom_pullHom, ha, hb, hc] using H

/-- A global linearization on the actual kernel-action scheme induces natural equivariant transport. -/
def toKernelLinearization : Kernel.Linearization.KernelLinearization f F L where
  transport := fun {_T} x y k hk => GlobalKernelLinearization.transport f F L D x y k hk
  unit_compat := fun {_T} x hx => transport_unit f F L D x hx
  mul_compat := fun {_T} x y z k l m hx hy hz hm => transport_mul f F L D x y z k l m hx hy hz hm
  pullback_compat := fun {_T _T'} g x y k hk x' y' k' hk' hx hy hkk =>
    transport_pullback f F L D g x y k hk x' y' k' hk' hx hy hkk

/-- The global kernel-action isomorphism produces ordinary descent data for the quotient map. -/
def toDescentData : F.DescentData (fun (_ : PUnit.{1}) => f) :=
  (toKernelLinearization f F L D).toDescentData

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization
