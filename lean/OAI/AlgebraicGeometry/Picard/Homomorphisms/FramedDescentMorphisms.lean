import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentComparison

/-! # Framed Descent Morphisms -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentMorphisms

noncomputable section

/-! Morphisms compatible with descent data remain compatible after
writing their matrices in global frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} {L M : X.Modules}

theorem unitEndPullback_framedMap (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (b : L ⟶ M) {T : Scheme.{u}} (x : T ⟶ X) :
    UnitPullbackScalars.Construction.unitEndPullback x (e.inv ≫ b ≫ d.hom) =
      (FramedDescentScalars.Construction.pulledModuleFrame e x).inv ≫ (Scheme.Modules.pullback x).map b ≫
        (FramedDescentScalars.Construction.pulledModuleFrame d x).hom := by
  simp only [UnitPullbackScalars.Construction.unitEndPullback, FramedDescentScalars.Construction.pulledModuleFrame, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]

variable {Y : Scheme.{u}} {f : X ⟶ Y} (D E : IntrinsicModuleDescent.Construction.NativeModuleDescent f)
variable (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (d : E.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

theorem framedDescent_morphism (b : D.module ⟶ E.module)
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (h : (Scheme.Modules.pullback x).map b ≫ E.hom q x y hx hy =
      D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map b) :
    UnitPullbackScalars.Construction.unitEndPullback x (e.inv ≫ b ≫ d.hom) ≫ FramedDescentScalars.Construction.framedDescentEnd E d q x y hx hy =
      FramedDescentScalars.Construction.framedDescentEnd D e q x y hx hy ≫ UnitPullbackScalars.Construction.unitEndPullback y (e.inv ≫ b ≫ d.hom) := by
  rw [unitEndPullback_framedMap, unitEndPullback_framedMap]
  simp only [FramedDescentScalars.Construction.framedDescentEnd, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback x).map b), h, Category.assoc]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentMorphisms
