import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionComposition

/-! # Extension Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits

noncomputable section

/-!
# Scalar-extension comparisons are determined on the original module's unit generators
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The original module inside its scalar extension. -/
def unit (f : R →+* S) (M : ModuleCat.{u} R) (m : M) : (extendScalars f).obj M :=
  (1 : S) ⊗ₜ[R,f] m

/-- Scalar-extension morphisms are determined on the original unit generators. -/
theorem hom_ext (f : R →+* S) (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} S} (a b : (extendScalars f).obj M ⟶ N)
    (h : ∀ m, a (unit f M m) = b (unit f M m)) : a = b := by
  apply ((extendRestrictScalarsAdj f).homEquiv M N).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h

/-- The unit generator in an iterated scalar extension. -/
def doubleUnit (f : R →+* S) (i : S →+* T) (M : ModuleCat.{u} R) (m : M) :
    (extendScalars i).obj ((extendScalars f).obj M) :=
  (1 : T) ⊗ₜ[S,i] (show (extendScalars f).obj M from (1 : S) ⊗ₜ[R,f] m)

/-- A transition identifies the two copies of every original module element. -/
def PreservesUnits (f : R →+* S) (i j : S →+* T) (M : ModuleCat.{u} R)
    (a : (extendScalars i).obj ((extendScalars f).obj M) ⟶
      (extendScalars j).obj ((extendScalars f).obj M)) : Prop :=
  ∀ m, a (doubleUnit f i M m) = doubleUnit f j M m

/-- Morphisms out of an iterated scalar extension are determined on these unit generators. -/
theorem iterated_hom_ext (f : R →+* S) (i : S →+* T) (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} T} (a b : (extendScalars i).obj ((extendScalars f).obj M) ⟶ N)
    (h : ∀ m, a (doubleUnit f i M m) = b (doubleUnit f i M m)) : a = b := by
  apply ((extendRestrictScalarsAdj i).homEquiv ((extendScalars f).obj M) N).injective
  apply ((extendRestrictScalarsAdj f).homEquiv M ((restrictScalars i).obj N)).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h

/-- Three transitions retaining the original module necessarily satisfy the cocycle. -/
theorem composition_eq_of_units (f : R →+* S) (i j k : S →+* T) (M : ModuleCat.{u} R)
    (a : (extendScalars i).obj ((extendScalars f).obj M) ⟶
      (extendScalars j).obj ((extendScalars f).obj M))
    (b : (extendScalars j).obj ((extendScalars f).obj M) ⟶
      (extendScalars k).obj ((extendScalars f).obj M))
    (c : (extendScalars i).obj ((extendScalars f).obj M) ⟶
      (extendScalars k).obj ((extendScalars f).obj M))
    (ha : PreservesUnits f i j M a) (hb : PreservesUnits f j k M b)
    (hc : PreservesUnits f i k M c) : a ≫ b = c := by
  apply iterated_hom_ext f i M
  intro m
  exact (congrArg (fun z => b z) (ha m)).trans ((hb m).trans (hc m).symm)

/-- The canonical composition comparison preserves original unit generators. -/
theorem composition_hom_unit (f : R →+* S) (i : S →+* T) (M : ModuleCat.{u} R) (m : M) :
    (extendScalarsComp f i).hom.app M (unit (i.comp f) M m) = doubleUnit f i M m :=
  ExtensionComposition.composition_hom_tmul f i M 1 m

/-- Its inverse recovers the unit generator in the composite extension. -/
theorem composition_inv_unit (f : R →+* S) (i : S →+* T) (M : ModuleCat.{u} R) (m : M) :
    (extendScalarsComp f i).inv.app M (doubleUnit f i M m) = unit (i.comp f) M m := by
  have h := ExtensionComposition.composition_inv_tmul f i M 1 1 m
  simp only [map_one, mul_one] at h
  exact h

/-- Extending a module morphism preserves its values on original unit generators. -/
theorem map_unit (f : R →+* S) {M N : ModuleCat.{u} R} (a : M ⟶ N) (m : M) :
    (extendScalars f).map a (unit f M m) = unit f N (a m) :=
  ExtendScalars.map_tmul f a 1 m

/-- Transport along equality of ring maps retains each pure tensor. -/
theorem transport_tmul {f g : R →+* S} (h : f = g) (M : ModuleCat.{u} R) (s : S) (m : M) :
    eqToHom (congrArg (fun i => (extendScalars i).obj M) h) (s ⊗ₜ[R,f] m) =
      s ⊗ₜ[R,g] m := by
  subst g
  rfl

/-- Equality of the last coordinate maps retains the original unit generator. -/
theorem transport_doubleUnit (f : R →+* S) {i j : S →+* T} (h : i = j)
    (M : ModuleCat.{u} R) (m : M) :
    eqToHom (congrArg (fun k => (extendScalars k).obj ((extendScalars f).obj M)) h)
        (doubleUnit f i M m) = doubleUnit f j M m := by
  subst j
  rfl

/-- Canonical gluing between two extensions whose coordinate maps agree on the original base. -/
def transition (f : R →+* S) (i j : S →+* T) (h : i.comp f = j.comp f) (M : ModuleCat.{u} R) :
    (extendScalars i).obj ((extendScalars f).obj M) ≅
      (extendScalars j).obj ((extendScalars f).obj M) :=
  ((extendScalarsComp f i).app M).symm ≪≫
    eqToIso (congrArg (fun k => (extendScalars k).obj M) h) ≪≫
      (extendScalarsComp f j).app M

/-- The canonical transition retains every original-module unit generator. -/
theorem transition_doubleUnit (f : R →+* S) (i j : S →+* T)
    (h : i.comp f = j.comp f) (M : ModuleCat.{u} R) (m : M) :
    (transition f i j h M).hom (doubleUnit f i M m) = doubleUnit f j M m := by
  change (extendScalarsComp f j).hom.app M
    (eqToHom (congrArg (fun k => (extendScalars k).obj M) h)
      ((extendScalarsComp f i).inv.app M
        ((1 : T) ⊗ₜ[S,i] (show (extendScalars f).obj M from (1 : S) ⊗ₜ[R,f] m)))) = _
  have hi := ExtensionComposition.composition_inv_tmul f i M 1 1 m
  simp only [map_one, mul_one] at hi
  have ht := transport_tmul h M 1 m
  have hj := ExtensionComposition.composition_hom_tmul f j M 1 m
  exact (congrArg (fun x => (extendScalarsComp f j).hom.app M
    (eqToHom (congrArg (fun k => (extendScalars k).obj M) h) x)) hi).trans
      ((congrArg (fun x => (extendScalarsComp f j).hom.app M x) ht).trans hj)

/-- The canonical transition identifies both copies of the entire original module. -/
theorem transition_preservesUnits (f : R →+* S) (i j : S →+* T)
    (h : i.comp f = j.comp f) (M : ModuleCat.{u} R) :
    PreservesUnits f i j M (transition f i j h M).hom :=
  transition_doubleUnit f i j h M

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits
