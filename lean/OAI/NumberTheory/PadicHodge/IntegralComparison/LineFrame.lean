import OAI.NumberTheory.PadicHodge.IntegralComparison.LineTrivializationCoboundary

/-! # Line Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrame.Comparison

noncomputable section

/-! An isomorphism of two globally defined lines compares their local
frames by a unit. Their normalized transition functions differ by the
coboundary of that actual unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

universe u

variable {X Y T : Scheme.{u}} (f : Y ⟶ X) {L M : X.Modules}
  (s : (Scheme.Modules.pullback f).obj L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
  (t : (Scheme.Modules.pullback f).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
  (e : L ≅ M)

def correction : Γ(Y, ⊤)ˣ :=
  AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.structureAutUnit (s.symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫ t)

theorem correction_spec :
    s.hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (correction f s t e).val =
      (Scheme.Modules.pullback f).map e.hom ≫ t.hom := by
  erw [correction, AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_structureAut]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]

def frameAt (p : T ⟶ Y) :=
  (Scheme.Modules.pullback p).mapIso s ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p

theorem correction_at (p : T ⟶ Y) :
    (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map e.hom) ≫
        (frameAt f t p).hom =
      (frameAt f s p).hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T)
        (p.appTop (correction f s t e).val) := by
  change (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map e.hom) ≫
      ((Scheme.Modules.pullback p).map t.hom ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom) =
    ((Scheme.Modules.pullback p).map s.hom ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, ← correction_spec f s t e, Functor.map_comp]
  rw [AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback, Category.assoc, AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality]
  simp only [Category.assoc]

theorem equation (p q : T ⟶ Y) (h : p ≫ f = q ≫ f)
    (dL dM : Γ(T, ⊤)ˣ)
    (hL : (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫ (frameAt f s q).hom =
      (frameAt f s p).hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) dL.val)
    (hM : (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app M ≫ (frameAt f t q).hom =
      (frameAt f t p).hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) dM.val) :
    Units.map p.appTop.hom.toMonoidHom (correction f s t e) * dM =
      dL * Units.map q.appTop.hom.toMonoidHom (correction f s t e) := by
  let u := correction f s t e
  have hn : (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map e.hom) ≫
        (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app M =
      (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫
        (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback f).map e.hom) :=
    (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.naturality e.hom
  have he : (frameAt f s p).hom ≫
        AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (p.appTop u.val * dM.val) =
      (frameAt f s p).hom ≫
        AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (dL.val * q.appTop u.val) := by
    calc
      _ = ((frameAt f s p).hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (p.appTop u.val)) ≫
          AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) dM.val := by rw [AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_mul, Category.assoc]
      _ = ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map e.hom) ≫
          (frameAt f t p).hom) ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) dM.val := by
        rw [← correction_at]
      _ = (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback f).map e.hom) ≫
          (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app M ≫ (frameAt f t q).hom := by
        rw [Category.assoc, ← hM]
      _ = (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫
          (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback f).map e.hom) ≫
            (frameAt f t q).hom := by rw [← Category.assoc, hn, Category.assoc]
      _ = (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫ (frameAt f s q).hom ≫
          AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (q.appTop u.val) := by rw [correction_at]
      _ = _ := by rw [← Category.assoc, hL, Category.assoc, ← AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_mul]
  apply Units.ext
  have hv := congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar
    ((cancel_epi (frameAt f s p).hom).mp he)
  change p.appTop.hom u.val * dM.val = dL.val * q.appTop.hom u.val
  simpa only [LineTrivializationCoboundary.scalar_value] using hv

theorem quotient_equation (p q : T ⟶ Y) (h : p ≫ f = q ≫ f)
    (dL dM : Γ(T, ⊤)ˣ)
    (hL : (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫ (frameAt f s q).hom =
      (frameAt f s p).hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) dL.val)
    (hM : (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app M ≫ (frameAt f t q).hom =
      (frameAt f t p).hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) dM.val) :
    dL / dM = Units.map p.appTop.hom.toMonoidHom (correction f s t e) /
      Units.map q.appTop.hom.toMonoidHom (correction f s t e) := by
  apply div_eq_div_iff_mul_eq_mul.mpr
  simpa only [mul_comm dM _] using (equation f s t e p q h dL dM hL hM).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrame.Comparison
