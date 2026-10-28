import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedRecovery

/-! # Framed Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedBaseChange.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: framed native descent scalars under arbitrary base change
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

/-- An iterated frame is exactly the frame through the canonical pullback comparison. -/
theorem pulledModuleFrame_iterated {X T U : Scheme.{u}} {M : X.Modules}
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (t : T ⟶ X) (x : U ⟶ T) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e t) x =
      (Scheme.Modules.pullbackComp x t).app M ≪≫ Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e (x ≫ t) := by
  apply Iso.ext
  exact (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame_comp e t x).symm

/-- The frame calculation is proved for abstract module objects before descent-data specialization. -/
theorem iteratedFrame_gluing {X U T : Scheme.{u}} {M : X.Modules}
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (t : U ⟶ X) (x y : T ⟶ U)
    (a : (Scheme.Modules.pullback (x ≫ t)).obj M ⟶ (Scheme.Modules.pullback (y ≫ t)).obj M)
    (b : (Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback t).obj M) ⟶
      (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback t).obj M))
    (hb : b = (Scheme.Modules.pullbackComp x t).hom.app M ≫ a ≫
      (Scheme.Modules.pullbackComp y t).inv.app M) :
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e t) x).inv ≫ b ≫
      (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e t) y).hom =
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e (x ≫ t)).inv ≫ a ≫ (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e (y ≫ t)).hom := by
  rw [pulledModuleFrame_iterated, pulledModuleFrame_iterated]
  apply FramedRecovery.Construction.LineDescent.conjugate_intertwiner ((Scheme.Modules.pullbackComp x t).app M)
    ((Scheme.Modules.pullbackComp y t).app M)
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e (x ≫ t)) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e (y ≫ t))
  rw [hb]
  change (Scheme.Modules.pullbackComp x t).hom.app M ≫ a =
    ((Scheme.Modules.pullbackComp x t).hom.app M ≫ a ≫
      (Scheme.Modules.pullbackComp y t).inv.app M) ≫ (Scheme.Modules.pullbackComp y t).hom.app M
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (s : Y' ⟶ Y) (t : X' ⟶ X) (w : t ≫ f = f' ≫ s)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- The full pulled datum has the usual pullback-composition formula at each test pair. -/
theorem nativeSquareDatum_hom {T : Scheme.{u}} (q : T ⟶ Y') (x y : T ⟶ X')
    (hx : x ≫ f' = q) (hy : y ≫ f' = q) :
    (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f' ((Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f f' s t w).obj D)).hom
      q x y hx hy =
    (Scheme.Modules.pullbackComp x t).hom.app (D.obj PUnit.unit) ≫
      (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D).hom (q ≫ s) (x ≫ t) (y ≫ t)
        (by rw [Category.assoc, w, ← Category.assoc, hx])
        (by rw [Category.assoc, w, ← Category.assoc, hy]) ≫
      (Scheme.Modules.pullbackComp y t).inv.app (D.obj PUnit.unit) := by
  cases hx
  rfl

/-- Framed descent scalars commute with every scheme square of covers. -/
theorem framedDescentScalar_square (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    {T : Scheme.{u}} (q : T ⟶ Y') (x y : T ⟶ X') (hx : x ≫ f' = q) (hy : y ≫ f' = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f' ((Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f f' s t w).obj D))
      (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e t) q x y hx hy =
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D) e (q ≫ s) (x ≫ t) (y ≫ t)
      (by rw [Category.assoc, w, ← Category.assoc, hx])
      (by rw [Category.assoc, w, ← Category.assoc, hy]) := by
  apply congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T)
  exact iteratedFrame_gluing e t x y _ _ (nativeSquareDatum_hom f f' s t w D q x y hx hy)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedBaseChange.Construction.LineDescent
