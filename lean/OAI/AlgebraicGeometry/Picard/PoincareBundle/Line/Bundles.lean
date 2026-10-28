import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Bundles -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

noncomputable section

/-!
# Line bundles for the PoincareBundle polarization descent construction

Line bundles here are actual sheaves of modules, locally isomorphic to
the structure sheaf. Pullback and its action on isomorphism classes are
constructed from the existing sheaf-of-modules pullback functor.
No descent, ampleness, or representability assertion is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

/-- The structure sheaf, considered as a module over itself. -/
def unitLine (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Inverse image of open sets preserves the whole space, hence is final. -/
theorem opensMap_final {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final := by
  let F := TopologicalSpace.Opens.map f.base
  have : PreservesLimit (Functor.empty.{0} Y.Opens) F :=
    preservesTerminal_of_iso F
      (F.mapIso (terminalIsTerminal.uniqueUpToIso isTerminalTop) ≪≫
        eqToIso (show F.obj (⊤ : Y.Opens) = (⊤ : X.Opens) from by ext; simp [F]) ≪≫
        isTerminalTop.uniqueUpToIso terminalIsTerminal)
  infer_instance

/-- Pullback preserves the trivial line bundle. -/
def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (unitLine Y) ≅ unitLine X := by
  have : (SheafOfModules.pushforward
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have := opensMap_final f
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  let e : (SheafOfModules.pullback f.toRingCatSheafHom).obj
      (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf :=
    asIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom)
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- A line bundle is locally free of rank one, expressed by local
isomorphisms with the structure sheaf on Zariski open neighborhoods. -/
def IsLine {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ unitLine U)

theorem isLine_unit (X : Scheme.{u}) : IsLine (unitLine X) := by
  intro x
  exact ⟨⊤, trivial, ⟨pullbackUnitIso (⊤ : X.Opens).ι⟩⟩

theorem IsLine.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : IsLine M) (e : M ≅ N) : IsLine N := by
  intro x
  obtain ⟨U, hx, ⟨hU⟩⟩ := hM x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ hU⟩⟩

/-- Local trivializations of a line bundle pull back along any morphism
of schemes, including inseparable morphisms. -/
theorem IsLine.pullback {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : IsLine M) (f : X ⟶ Y) : IsLine ((Scheme.Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hx, ⟨eU⟩⟩ := hM (f x)
  refine ⟨f ⁻¹ᵁ U, hx, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso eU ≪≫
    pullbackUnitIso (f ∣_ U)

/-- A genuine algebraic line bundle with its local-freeness property. -/
structure LineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  isLine : IsLine sheaf

namespace LineBundle

def trivial (X : Scheme.{u}) : LineBundle X := ⟨unitLine X, isLine_unit X⟩

def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) : LineBundle X :=
  ⟨(Scheme.Modules.pullback f).obj L.sheaf, L.isLine.pullback f⟩

/-- Isomorphism of the actual module sheaves, independent of choices
of local trivialization. -/
def isoSetoid (X : Scheme.{u}) : Setoid (LineBundle X) where
  r L M := Nonempty (L.sheaf ≅ M.sheaf)
  iseqv := ⟨fun L => ⟨Iso.refl L.sheaf⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨d⟩ => ⟨e ≪≫ d⟩⟩

end LineBundle

/-- Isomorphism classes of algebraic line bundles. The tensor product
group structure is not built into this definition. -/
def LineBundleClass (X : Scheme.{u}) := Quotient (LineBundle.isoSetoid X)

namespace LineBundleClass

def mk {X : Scheme.{u}} (L : LineBundle X) : LineBundleClass X := Quotient.mk _ L

def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) : LineBundleClass Y → LineBundleClass X :=
  Quotient.map (LineBundle.pullback f) (fun _ _ ⟨e⟩ =>
    ⟨(Scheme.Modules.pullback f).mapIso e⟩)

@[simp]
theorem pullback_mk {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    LineBundleClass.pullback f (LineBundleClass.mk L) = LineBundleClass.mk (L.pullback f) := rfl

@[simp]
theorem pullback_id {X : Scheme.{u}} (L : LineBundleClass X) :
    LineBundleClass.pullback (𝟙 X) L = L := by
  induction L using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      exact ⟨(Scheme.Modules.pullbackId X).app L.sheaf⟩

theorem pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : LineBundleClass Z) : LineBundleClass.pullback (f ≫ g) L = LineBundleClass.pullback f (LineBundleClass.pullback g L) := by
  induction L using Quotient.inductionOn with
  | _ L =>
      apply Quotient.sound
      exact ⟨((Scheme.Modules.pullbackComp f g).app L.sheaf).symm⟩

end LineBundleClass

/-- The presheaf of isomorphism classes of algebraic line bundles.
Relative Picard functors additionally quotient by bundles from the base
and sheafify; neither operation is silently assumed here. -/
def lineBundleClassFunctor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj X := LineBundleClass X.unop
  map f := ↾(LineBundleClass.pullback f.unop)
  map_id X := by ext L; exact LineBundleClass.pullback_id L
  map_comp f g := by ext L; exact LineBundleClass.pullback_comp g.unop f.unop L

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
