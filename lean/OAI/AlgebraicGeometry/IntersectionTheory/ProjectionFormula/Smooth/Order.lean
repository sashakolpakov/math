import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Order
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction
import Mathlib.RingTheory.KrullDimension.Field

/-! # Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Order

noncomputable section

/-! A smooth morphism preserves the native integer order at a
codimension-one point mapping to a codimension-one point. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

universe u

theorem maximalIdeal_map (R S : Type u) [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [IsDomain S] [Ring.KrullDimLE 1 S]
    (σ : R →+* S) (hR : IsLocalRing.maximalIdeal R ≠ ⊥) (hinj : Function.Injective σ)
    [IsDomain (S ⧸ (IsLocalRing.maximalIdeal R).map σ)] :
    (IsLocalRing.maximalIdeal R).map σ = IsLocalRing.maximalIdeal S := by
  let J := (IsLocalRing.maximalIdeal R).map σ
  have hp : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  have hn : J ≠ ⊥ := by
    obtain ⟨a, ha, hane⟩ := (Submodule.ne_bot_iff (IsLocalRing.maximalIdeal R)).mp hR
    intro hz
    have h : σ a ∈ J := Ideal.mem_map_of_mem σ ha
    rw [hz, Ideal.mem_bot] at h
    exact hane (hinj (h.trans σ.map_zero.symm))
  exact IsLocalRing.eq_maximalIdeal (hp.isMaximal_of_ne_bot hn)

theorem ord_smooth {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Smooth f] (hη : f (genericPoint X) = genericPoint Y)
    (x : X) (hx : coheight x = 1) (hy : coheight (f x) = 1) (g : Y.functionField) :
    X.ord (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g) x = Y.ord g (f x) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap R S) := f.toLRSHom.prop x
  let : Module.Flat R S := Flat.stalkMap f x
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hy.le
  let : Ring.KrullDimLE 1 S := krullDimLE_of_coheight_le hx.le
  let : IsDomain (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    StalkFiber.quotient_domain f x
  have hinj : Function.Injective (algebraMap R S) := by
    intro a b hab
    apply IsFractionRing.injective R Y.functionField
    apply (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.injective
    rw [Divisor.DivisorRestriction.genericFieldMap_stalk, Divisor.DivisorRestriction.genericFieldMap_stalk]
    exact congrArg (algebraMap S X.functionField) hab
  have hn : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro h
    have hf : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr h
    have hd := ringKrullDim_eq_zero_of_isField hf
    rw [ringKrullDim_stalk_eq_coheight, hy] at hd
    exact one_ne_zero hd
  have hm := maximalIdeal_map R S (algebraMap R S) hn hinj
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
  exact congrArg WithZero.log (ProjectionFormula.Flat.Order.ordFrac_eq R S hm hinj
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom (Divisor.DivisorRestriction.genericFieldMap_stalk f hη x) g)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Order
