import OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

/-! # Line Trivialization Coboundary -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LineTrivializationCoboundary

noncomputable section

/-! A global trivialization of a descended line makes its original
unit-valued transition function a coboundary. The equation uses the
actual pullback functors and the actual maps on regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

universe u

variable {X Y T : Scheme.{u}} (f : Y ⟶ X) {L : X.Modules}
  (t : (Scheme.Modules.pullback f).obj L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
  (e : L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

def correction : Γ(Y, ⊤)ˣ :=
  AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.structureAutUnit (t.symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f)

theorem correction_spec :
    t.hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (correction f t e).val =
      (Scheme.Modules.pullback f).map e.hom ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
  erw [correction, AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_structureAut]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]

theorem scalar_value (r : Γ(T, ⊤)) :
    AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar (AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) r) = r := by
  simp [AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar, AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_apply]

theorem equation (p q : T ⟶ Y) (h : p ≫ f = q ≫ f)
    (s : (Scheme.Modules.pullback p).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≅
      (Scheme.Modules.pullback q).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) (d : Γ(T, ⊤)ˣ)
    (ht : (Scheme.Modules.pullback p).map t.hom ≫ s.hom =
      (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫ (Scheme.Modules.pullback q).map t.hom)
    (hs : s.hom ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) d.val) :
    Units.map p.appTop.hom.toMonoidHom (correction f t e) =
      d * Units.map q.appTop.hom.toMonoidHom (correction f t e) := by
  let u := correction f t e
  let P := Scheme.Modules.pullback p
  let Q := Scheme.Modules.pullback q
  have hn : P.map (t.hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) u.val) ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom =
      (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫
        Q.map (t.hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) u.val) ≫
          (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom := by
    dsimp only [u, P, Q]
    rw [correction_spec, Functor.map_comp, Category.assoc,
      AlgebraicGeometry.Picard.PoincareBundle.StructureUnitGluing.unit_gluing f p q h]
    rw [Functor.map_comp]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun a => a ≫ (Scheme.Modules.pullback q).map
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom)
        ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.naturality e.hom)
  have hu : P.map (AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) u.val) ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom =
      s.hom ≫ Q.map (AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) u.val) ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom := by
    apply (cancel_epi (P.map t.hom)).mp
    calc
      _ = P.map (t.hom ≫ AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) u.val) ≫
          (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom := by rw [Functor.map_comp, Category.assoc]
      _ = _ := hn
      _ = _ := by
        have ht' : (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫ Q.map t.hom =
            P.map t.hom ≫ s.hom := ht.symm
        simp only [Functor.map_comp, ← Category.assoc]
        erw [ht']
  have he :
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom ≫
        AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (p.appTop u.val) =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom ≫
        AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (d.val * q.appTop u.val) := by
    calc
      _ = P.map (AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) u.val) ≫
          (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom := by
        rw [AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback, AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality]
      _ = _ := hu
      _ = (s.hom ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom) ≫
          AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (q.appTop u.val) := by
        rw [AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback, AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality, Category.assoc]
      _ = _ := by rw [hs, AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_mul, Category.assoc]
  apply Units.ext
  have hv := congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar
    ((cancel_epi (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom).mp he)
  change p.appTop.hom u.val = d.val * q.appTop.hom u.val
  simpa only [scalar_value] using hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LineTrivializationCoboundary
