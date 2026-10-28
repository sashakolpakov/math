import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SchemeUniversalTrivialization

/-! # Frame Scalar -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar

noncomputable section

/-! Evaluating a line-bundle frame along a rigidified section produces
an actual invertible global function. Normalization is the equation
that this function equals one. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

def rigidificationBaseChangeIso {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback f).obj M) ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T :=
  (Scheme.Modules.pullbackComp b f).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp g s).app M).symm ≪≫
      (Scheme.Modules.pullback g).mapIso r ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g

def frameAxisIso {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).symm ≪≫ (Scheme.Modules.pullback b).mapIso e ≪≫
    rigidificationBaseChangeIso f b g s h M r

def frameAxisScalar {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) : Γ(T, ⊤) :=
  AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (frameAxisIso f b g s h M r e).hom

theorem frameAxisScalar_isUnit {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    IsUnit (frameAxisScalar f b g s h M r e) :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff (frameAxisIso f b g s h M r e).hom).mp inferInstance

theorem frameAxisScalar_eq_one_iff {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    frameAxisScalar f b g s h M r e = 1 ↔ (frameAxisIso f b g s h M r e).hom = 𝟙 _ := by
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (frameAxisIso f b g s h M r e).hom =
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (𝟙 _) ↔ _
  exact (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective T).eq_iff

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar
