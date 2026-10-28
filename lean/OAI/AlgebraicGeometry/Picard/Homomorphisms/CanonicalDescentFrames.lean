import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle

/-! # Canonical Descent Frames -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames

noncomputable section

/-! Native formulas for the canonical descent datum of a pulled-back
line bundle, and its trivialization by a frame on the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)

def canonicalModuleDescent : IntrinsicModuleDescent.Construction.NativeModuleDescent f :=
  IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f
    ((PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L)

theorem modulePullbacks_mapComp_inv {T : Scheme.{u}} (q : T ⟶ Y)
    (x : T ⟶ X) (hx : x ≫ f = q) :
    (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.mapComp' f.op.toLoc x.op.toLoc q.op.toLoc
      (by exact congrArg (fun a : T ⟶ Y => a.op.toLoc) hx)).inv.toNatTrans.app L =
      (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app L := by
  cases hx
  simp only [Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.trans_refl]
  rfl

theorem modulePullbacks_mapComp_hom {T : Scheme.{u}} (q : T ⟶ Y)
    (x : T ⟶ X) (hx : x ≫ f = q) :
    (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.mapComp' f.op.toLoc x.op.toLoc q.op.toLoc
      (by exact congrArg (fun a : T ⟶ Y => a.op.toLoc) hx)).hom.toNatTrans.app L =
      (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).inv.app L := by
  cases hx
  simp only [Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.trans_refl]
  rfl

theorem canonicalModuleDescent_hom {T : Scheme.{u}} (q : T ⟶ Y)
    (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (canonicalModuleDescent f L).hom q x y hx hy =
      (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app L ≫
        (Scheme.Modules.pullbackComp y f ≪≫ Scheme.Modules.pullbackCongr hy).inv.app L := by
  change (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.mapComp' f.op.toLoc x.op.toLoc q.op.toLoc _).inv.toNatTrans.app L ≫
    (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.mapComp' f.op.toLoc y.op.toLoc q.op.toLoc _).hom.toNatTrans.app L = _
  exact congrArg₂ (· ≫ ·) (modulePullbacks_mapComp_inv f L q x hx)
    (modulePullbacks_mapComp_hom f L q y hy)

theorem pulledModuleFrame_composite (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
    {T : Scheme.{u}} (q : T ⟶ Y) (x : T ⟶ X) (hx : x ≫ f = q) :
    (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app L ≫
        (FramedDescentScalars.Construction.pulledModuleFrame e q).hom =
      (FramedDescentScalars.Construction.pulledModuleFrame (FramedDescentScalars.Construction.pulledModuleFrame e f) x).hom := by
  cases hx
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
  exact FramedDescentScalars.Construction.pulledModuleFrame_comp e f x

theorem canonicalModuleDescent_framedEnd (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    FramedDescentScalars.Construction.framedDescentEnd (canonicalModuleDescent f L) (FramedDescentScalars.Construction.pulledModuleFrame e f) q x y hx hy = 𝟙 _ := by
  let Cx := (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).app L
  let Cy := (Scheme.Modules.pullbackComp y f ≪≫ Scheme.Modules.pullbackCongr hy).app L
  let Fx := FramedDescentScalars.Construction.pulledModuleFrame (FramedDescentScalars.Construction.pulledModuleFrame e f) x
  let Fy := FramedDescentScalars.Construction.pulledModuleFrame (FramedDescentScalars.Construction.pulledModuleFrame e f) y
  have hnorm : FramedDescentScalars.Construction.framedDescentEnd (canonicalModuleDescent f L) (FramedDescentScalars.Construction.pulledModuleFrame e f) q x y hx hy =
      Fx.inv ≫ (Cx.hom ≫ Cy.inv) ≫ Fy.hom :=
    congrArg (fun a : (Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback f).obj L) ⟶
      (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback f).obj L) => Fx.inv ≫ a ≫ Fy.hom)
        (canonicalModuleDescent_hom f L q x y hx hy)
  have hframe : (Cx.hom ≫ Cy.inv) ≫ Fy.hom = Fx.hom := by
    change (Cx.hom ≫ Cy.inv) ≫ (FramedDescentScalars.Construction.pulledModuleFrame (FramedDescentScalars.Construction.pulledModuleFrame e f) y).hom = _
    rw [← pulledModuleFrame_composite f L e q y hy]
    change (Cx.hom ≫ Cy.inv) ≫ (Cy.hom ≫ (FramedDescentScalars.Construction.pulledModuleFrame e q).hom) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact pulledModuleFrame_composite f L e q x hx
  exact hnorm.trans ((congrArg (fun a => Fx.inv ≫ a) hframe).trans Fx.inv_hom_id)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames
