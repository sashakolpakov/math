import OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationComparisonPasting
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SchemeNaturality

/-! # Rigidification Scalar Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationScalarNaturality

noncomputable section

/-! The actual rigidification scalar of a frame commutes with base
change, including the canonical comparison of the pulled-back line bundle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

theorem compositeLineFrameIso_hom {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y) (M : X.Modules)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    (Frame.SchemeNaturality.Construction.compositeLineFrameIso f j M e).hom =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j e.hom ≫ (Scheme.Modules.pullbackComp j f).hom.app M := by
  simp only [Frame.SchemeNaturality.Construction.compositeLineFrameIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Category.assoc]

theorem frameAxisIso_hom {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    (Rigidified.FrameScalar.Construction.frameAxisIso f b g s h M r e).hom =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b e.hom ≫ (Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom := by
  simp only [Rigidified.FrameScalar.Construction.frameAxisIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Category.assoc]

theorem frameAxisScalar_baseChange {X Y Z S T U : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (s : S ⟶ X) (b : T ⟶ Y) (g : T ⟶ S)
    (c : U ⟶ Z) (t : U ⟶ T) (h : c ≫ j = t ≫ b) (h₀ : b ≫ f = g ≫ s)
    (h₁ : c ≫ (j ≫ f) = (t ≫ g) ≫ s) (M : X.Modules)
    (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    Rigidified.FrameScalar.Construction.frameAxisScalar (j ≫ f) c (t ≫ g) s h₁ M r (Frame.SchemeNaturality.Construction.compositeLineFrameIso f j M e) =
      t.appTop (Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h₀ M r e) := by
  have he : (Rigidified.FrameScalar.Construction.frameAxisIso (j ≫ f) c (t ≫ g) s h₁ M r (Frame.SchemeNaturality.Construction.compositeLineFrameIso f j M e)).hom =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection t (Rigidified.FrameScalar.Construction.frameAxisIso f b g s h₀ M r e).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom := by
    rw [frameAxisIso_hom, compositeLineFrameIso_hom, PullbackStructureComparison.Construction.pullbackSection_targetMap, Category.assoc,
      RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_paste f j s b g c t h h₀ h₁ M r]
    rw [reassoc_of% (PullbackStructureComparison.Construction.pullbackSection_square j b c t h ((Scheme.Modules.pullback f).obj M) e.hom)]
    rw [← PullbackStructureComparison.Construction.pullbackSection_targetMap_assoc, ← frameAxisIso_hom]
  have hv : AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection t (Rigidified.FrameScalar.Construction.frameAxisIso f b g s h₀ M r e).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom) =
      t.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (Rigidified.FrameScalar.Construction.frameAxisIso f b g s h₀ M r e).hom) := by
    change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U (((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).inv ≫
      (Scheme.Modules.pullback t).map (Rigidified.FrameScalar.Construction.frameAxisIso f b g s h₀ M r e).hom) ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom) = _
    rw [Category.assoc]
    exact Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback t (Rigidified.FrameScalar.Construction.frameAxisIso f b g s h₀ M r e).hom
  exact (congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U) he).trans hv

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationScalarNaturality
