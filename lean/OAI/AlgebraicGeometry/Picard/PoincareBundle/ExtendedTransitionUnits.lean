import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits

/-! # Extended Transition Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtendedTransitionUnits

noncomputable section

/-!
# Scalar extension retains the original unit generators of a gluing map
-/

open _root_.CategoryTheory _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits

variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]

/-- Extend a transition using the standard composition comparisons. -/
def extend (i j : S →+* T) (k : T →+* U) (X : ModuleCat.{u} S)
    (a : (extendScalars i).obj X ⟶ (extendScalars j).obj X) :
    (extendScalars (k.comp i)).obj X ⟶ (extendScalars (k.comp j)).obj X :=
  (extendScalarsComp i k).hom.app X ≫ (extendScalars k).map a ≫
    (extendScalarsComp j k).inv.app X

/-- Extending a transition preserves every unit on which the transition agrees. -/
theorem extend_unit (i j : S →+* T) (k : T →+* U) (X : ModuleCat.{u} S)
    (a : (extendScalars i).obj X ⟶ (extendScalars j).obj X)
    (x : X) (h : a (Scalar.ExtensionUnits.unit i X x) = Scalar.ExtensionUnits.unit j X x) :
    extend i j k X a (Scalar.ExtensionUnits.unit (k.comp i) X x) = Scalar.ExtensionUnits.unit (k.comp j) X x := by
  change (extendScalarsComp j k).inv.app X
    ((extendScalars k).map a ((extendScalarsComp i k).hom.app X
      (Scalar.ExtensionUnits.unit (k.comp i) X x))) = _
  have h₁ := Scalar.ExtensionUnits.composition_hom_unit i k X x
  have h₂ := Scalar.ExtensionUnits.map_unit k a (Scalar.ExtensionUnits.unit i X x)
  have h₃ := congrArg (Scalar.ExtensionUnits.unit k ((extendScalars j).obj X)) h
  have h₄ := Scalar.ExtensionUnits.composition_inv_unit j k X x
  exact (congrArg (fun z => (extendScalarsComp j k).inv.app X
    ((extendScalars k).map a z)) h₁).trans
      ((congrArg (fun z => (extendScalarsComp j k).inv.app X z) (h₂.trans h₃)).trans h₄)

/-- The same fact for a module already pulled back from its original base ring. -/
theorem extend_doubleUnit (f : R →+* S) (i j : S →+* T) (k : T →+* U)
    (M : ModuleCat.{u} R)
    (a : (extendScalars i).obj ((extendScalars f).obj M) ⟶
      (extendScalars j).obj ((extendScalars f).obj M))
    (m : M) (h : a (Scalar.ExtensionUnits.doubleUnit f i M m) = Scalar.ExtensionUnits.doubleUnit f j M m) :
    extend i j k ((extendScalars f).obj M) a (Scalar.ExtensionUnits.doubleUnit f (k.comp i) M m) =
      Scalar.ExtensionUnits.doubleUnit f (k.comp j) M m :=
  extend_unit i j k ((extendScalars f).obj M) a (Scalar.ExtensionUnits.unit f M m) h

/-- Identifying the endpoint coordinate maps also preserves these unit generators. -/
theorem transported_extend_doubleUnit (f : R →+* S) (i j : S →+* T) (k : T →+* U)
    (l n : S →+* U) (hi : k.comp i = l) (hj : k.comp j = n)
    (M : ModuleCat.{u} R)
    (a : (extendScalars i).obj ((extendScalars f).obj M) ⟶
      (extendScalars j).obj ((extendScalars f).obj M))
    (m : M) (h : a (Scalar.ExtensionUnits.doubleUnit f i M m) = Scalar.ExtensionUnits.doubleUnit f j M m) :
    (eqToHom (congrArg (fun t => (extendScalars t).obj ((extendScalars f).obj M)) hi.symm) ≫
      extend i j k ((extendScalars f).obj M) a ≫
      eqToHom (congrArg (fun t => (extendScalars t).obj ((extendScalars f).obj M)) hj))
        (Scalar.ExtensionUnits.doubleUnit f l M m) = Scalar.ExtensionUnits.doubleUnit f n M m := by
  subst l
  subst n
  change extend i j k ((extendScalars f).obj M) a (Scalar.ExtensionUnits.doubleUnit f (k.comp i) M m) = _
  exact extend_doubleUnit f i j k M a m h

/-- Scalar extension retains the entire original module across a transition. -/
theorem extend_preservesUnits (f : R →+* S) (i j : S →+* T) (k : T →+* U)
    (M : ModuleCat.{u} R)
    (a : (extendScalars i).obj ((extendScalars f).obj M) ⟶
      (extendScalars j).obj ((extendScalars f).obj M)) (h : Scalar.ExtensionUnits.PreservesUnits f i j M a) :
    Scalar.ExtensionUnits.PreservesUnits f (k.comp i) (k.comp j) M (extend i j k ((extendScalars f).obj M) a) :=
  fun m => extend_doubleUnit f i j k M a m (h m)

/-- Endpoint identifications retain the same property after scalar extension. -/
theorem transported_extend_preservesUnits (f : R →+* S) (i j : S →+* T) (k : T →+* U)
    (l n : S →+* U) (hi : k.comp i = l) (hj : k.comp j = n)
    (M : ModuleCat.{u} R)
    (a : (extendScalars i).obj ((extendScalars f).obj M) ⟶
      (extendScalars j).obj ((extendScalars f).obj M)) (h : Scalar.ExtensionUnits.PreservesUnits f i j M a) :
    Scalar.ExtensionUnits.PreservesUnits f l n M
      (eqToHom (congrArg (fun t => (extendScalars t).obj ((extendScalars f).obj M)) hi.symm) ≫
        extend i j k ((extendScalars f).obj M) a ≫
        eqToHom (congrArg (fun t => (extendScalars t).obj ((extendScalars f).obj M)) hj)) :=
  fun m => transported_extend_doubleUnit f i j k l n hi hj M a m (h m)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtendedTransitionUnits
