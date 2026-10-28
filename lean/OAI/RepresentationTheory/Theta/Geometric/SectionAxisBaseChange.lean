import OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationScalarNaturality

/-! # Section Axis Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.SectionAxisBaseChange

noncomputable section

/-! Axis values of arbitrary line-bundle sections, before any frame
condition, commute with actual geometric base change. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationScalarNaturality.Construction

universe u

def sectionAxisEnd {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj M) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b e ≫ (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom

def sectionAxisScalar {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj M) : Γ(T, ⊤) :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (sectionAxisEnd f b g s h M r e)

theorem sectionAxisEnd_baseChange {X Y Z S T U : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (s : S ⟶ X) (b : T ⟶ Y) (g : T ⟶ S)
    (c : U ⟶ Z) (t : U ⟶ T) (h : c ≫ j = t ≫ b) (h₀ : b ≫ f = g ≫ s)
    (h₁ : c ≫ (j ≫ f) = (t ≫ g) ≫ s) (M : X.Modules)
    (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj M) :
    sectionAxisEnd (j ≫ f) c (t ≫ g) s h₁ M r
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j e ≫ (Scheme.Modules.pullbackComp j f).hom.app M) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection t (sectionAxisEnd f b g s h₀ M r e) ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom := by
  unfold sectionAxisEnd
  rw [AlgebraicGeometry.FormalGeometry.Completion.PullbackStructureComparison.Construction.pullbackSection_targetMap, Category.assoc,
    AlgebraicGeometry.FormalGeometry.Completion.RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_paste f j s b g c t h h₀ h₁ M r]
  rw [reassoc_of% (AlgebraicGeometry.FormalGeometry.Completion.PullbackStructureComparison.Construction.pullbackSection_square j b c t h ((Scheme.Modules.pullback f).obj M) e)]
  rw [← AlgebraicGeometry.FormalGeometry.Completion.PullbackStructureComparison.Construction.pullbackSection_targetMap_assoc]

theorem sectionAxisScalar_baseChange {X Y Z S T U : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (s : S ⟶ X) (b : T ⟶ Y) (g : T ⟶ S)
    (c : U ⟶ Z) (t : U ⟶ T) (h : c ≫ j = t ≫ b) (h₀ : b ≫ f = g ≫ s)
    (h₁ : c ≫ (j ≫ f) = (t ≫ g) ≫ s) (M : X.Modules)
    (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj M) :
    sectionAxisScalar (j ≫ f) c (t ≫ g) s h₁ M r
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j e ≫ (Scheme.Modules.pullbackComp j f).hom.app M) =
      t.appTop (sectionAxisScalar f b g s h₀ M r e) := by
  unfold sectionAxisScalar
  rw [sectionAxisEnd_baseChange f j s b g c t h h₀ h₁ M r e]
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U (((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).inv ≫
    (Scheme.Modules.pullback t).map (sectionAxisEnd f b g s h₀ M r e)) ≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom) = _
  rw [Category.assoc]
  exact AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback t (sectionAxisEnd f b g s h₀ M r e)

theorem sectionAxisScalar_frame {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    sectionAxisScalar f b g s h M r e.hom = AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e :=
  congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) (AlgebraicGeometry.FormalGeometry.Completion.RigidificationScalarNaturality.Construction.frameAxisIso_hom f b g s h M r e).symm

end

end OAI.RepresentationTheory.Theta.Geometric.SectionAxisBaseChange
