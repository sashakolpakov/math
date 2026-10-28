import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

noncomputable section

/-!
Line bundles over arbitrary schemes and their contravariant functor of
isomorphism classes. These are actual sheaves of modules locally isomorphic
to the structure sheaf, not abstract polarization parameters.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The structure sheaf considered as a sheaf of modules over itself. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Pullback preserves the structure module. -/
def structureModulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have : (Functor.fromPUnit.{0} (⊤ : Y.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal CategoryTheory.Limits.isTerminalTop
  have : (Functor.fromPUnit.{0} (⊤ : X.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal CategoryTheory.Limits.isTerminalTop
  have : ((Functor.fromPUnit.{0} (⊤ : Y.Opens)) ⋙
      TopologicalSpace.Opens.map f.base).Final :=
    Functor.final_of_natIso (F := Functor.fromPUnit.{0} (⊤ : X.Opens))
      (Discrete.natIso (fun _ => Iso.refl _))
  have : (TopologicalSpace.Opens.map f.base).Final :=
    Functor.final_of_final_comp (Functor.fromPUnit.{0} (⊤ : Y.Opens)) _
  have := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :
    (SheafOfModules.pullback f.toRingCatSheafHom).obj
        (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

/-- An algebraic line bundle over an arbitrary scheme. -/
structure LineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  locallyTrivial : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj sheaf ≅ structureModule U.toScheme)

namespace LineBundle

variable {X Y Z : Scheme.{u}}

/-- The trivial line bundle. -/
def trivial (X : Scheme.{u}) : LineBundle X where
  sheaf := structureModule X
  locallyTrivial x := ⟨⊤, by trivial, ⟨structureModulePullbackIso _⟩⟩

/-- Base change of a line bundle, with local triviality proved by pulling
back its frames to the preimages of the trivializing opens. -/
def pullback (f : X ⟶ Y) (L : LineBundle Y) : LineBundle X where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial (f x)
    refine ⟨f ⁻¹ᵁ U, hx, ⟨?_⟩⟩
    exact (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm.app L.sheaf ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
      structureModulePullbackIso (f ∣_ U)

/-- Isomorphism of line bundles is isomorphism of their module sheaves. -/
def isoSetoid (X : Scheme.{u}) : Setoid (LineBundle X) where
  r L M := Nonempty (L.sheaf ≅ M.sheaf)
  iseqv := {
    refl L := ⟨Iso.refl L.sheaf⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩ }

/-- Isomorphism classes of actual algebraic line bundles. -/
def IsoClass (X : Scheme.{u}) := Quotient (isoSetoid X)

/-- The isomorphism class of a line bundle. -/
def classOf (L : LineBundle X) : IsoClass X := Quotient.mk _ L

/-- The class of the structure sheaf. -/
def trivialClass (X : Scheme.{u}) : IsoClass X := Quotient.mk _ (LineBundle.trivial X)

/-- Pullback on isomorphism classes does not depend on the representative. -/
def pullbackClass (f : X ⟶ Y) : IsoClass Y → IsoClass X :=
  Quotient.map (LineBundle.pullback f) (fun _ _ ⟨e⟩ =>
    ⟨(Scheme.Modules.pullback f).mapIso e⟩)

@[simp]
theorem pullbackClass_trivial (f : X ⟶ Y) :
    pullbackClass f (trivialClass Y) = trivialClass X := by
  apply Quotient.sound
  exact ⟨structureModulePullbackIso f⟩

@[simp]
theorem pullbackClass_id (q : IsoClass X) : pullbackClass (𝟙 X) q = q := by
  refine Quotient.inductionOn q (fun L => ?_)
  apply Quotient.sound
  exact ⟨(Scheme.Modules.pullbackId X).app L.sheaf⟩

theorem pullbackClass_comp (f : X ⟶ Y) (g : Y ⟶ Z) (q : IsoClass Z) :
    pullbackClass (f ≫ g) q = pullbackClass f (pullbackClass g q) := by
  refine Quotient.inductionOn q (fun L => ?_)
  apply Quotient.sound
  exact ⟨(Scheme.Modules.pullbackComp f g).symm.app L.sheaf⟩

/-- Pullback along an isomorphism gives an equivalence on line-bundle classes. -/
def pullbackIso (e : X ≅ Y) : IsoClass Y ≃ IsoClass X where
  toFun := pullbackClass e.hom
  invFun := pullbackClass e.inv
  left_inv q := (pullbackClass_comp e.inv e.hom q).symm.trans
    ((congrArg (fun f : Y ⟶ Y => pullbackClass f q) e.inv_hom_id).trans
      (pullbackClass_id q))
  right_inv q := (pullbackClass_comp e.hom e.inv q).symm.trans
    ((congrArg (fun f : X ⟶ X => pullbackClass f q) e.hom_inv_id).trans
      (pullbackClass_id q))

end LineBundle

/-- The contravariant functor of isomorphism classes of line bundles. -/
def lineBundleClassFunctor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj X := LineBundle.IsoClass X.unop
  map f := TypeCat.ofHom (LineBundle.pullbackClass f.unop)
  map_id X := by
    ext q
    exact LineBundle.pullbackClass_id q
  map_comp f g := by
    ext q
    exact LineBundle.pullbackClass_comp g.unop f.unop q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
