import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SquareSectionComposition
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionLineIsomorphism
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionBaseChange

/-! # Norm Square Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSquareComposition.Construction

noncomputable section

/-! Norm sections transported to the original line-power sheaf agree
under successive affine base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def normSquareSection {X Y X' Y' : Scheme.{u}}
    (q : X ⟶ Y) (q' : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (h : j ≫ q = q' ≫ i) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' ≅ (L.pullback i).sheaf) (d : ℕ)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' ⟶ ((L.tensorPower d).pullback i).sheaf :=
  FramedNormSection.Construction.framedNormSection q' e.hom d (SquareSectionComposition.Construction.pullbackSquareSection q q' j i h z) ≫
    (L.powerBaseChangeIso i d).inv

def compositeNormFrame {Y Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ Y) (i₂ : Y₂ ⟶ Y₁)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y₁ ≅ (L.pullback i₁).sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y₂ ≅ (L.pullback (i₂ ≫ i₁)).sheaf :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso i₂).symm ≪≫ (Scheme.Modules.pullback i₂).mapIso e ≪≫
    (Scheme.Modules.pullbackComp i₂ i₁).app L.sheaf

set_option backward.isDefEq.respectTransparency false in
theorem normSquareSection_comp
    {X Y X₁ Y₁ X₂ Y₂ : Scheme.{u}}
    [IsAffine X₁] [IsAffine Y₁] [IsAffine X₂] [IsAffine Y₂]
    (q : X ⟶ Y) (q₁ : X₁ ⟶ Y₁) (q₂ : X₂ ⟶ Y₂)
    (j₁ : X₁ ⟶ X) (i₁ : Y₁ ⟶ Y) (j₂ : X₂ ⟶ X₁) (i₂ : Y₂ ⟶ Y₁)
    (h₁ : j₁ ≫ q = q₁ ≫ i₁) (hs : IsPullback j₂ q₂ q₁ i₂)
    (hc : (j₂ ≫ j₁) ≫ q = q₂ ≫ (i₂ ≫ i₁))
    {ι : Type v} [Fintype ι]
    (b : letI := q₁.appTop.hom.toAlgebra; Module.Basis ι Γ(Y₁, ⊤) Γ(X₁, ⊤))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y₁ ≅ (L.pullback i₁).sheaf) (d : ℕ)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ (normSquareSection q q₁ j₁ i₁ h₁ L e d z) ≫
        (Scheme.Modules.pullbackComp i₂ i₁).hom.app (L.tensorPower d).sheaf =
      normSquareSection q q₂ (j₂ ≫ j₁) (i₂ ≫ i₁) hc L (compositeNormFrame i₁ i₂ L e) d z := by
  let z₁ := SquareSectionComposition.Construction.pullbackSquareSection q q₁ j₁ i₁ h₁ z
  let z₂ := SquareSectionComposition.Construction.pullbackSquareSection q₁ q₂ j₂ i₂ hs.w z₁
  let zc := SquareSectionComposition.Construction.pullbackSquareSection q q₂ (j₂ ≫ j₁) (i₂ ≫ i₁) hc z
  let c := (Scheme.Modules.pullbackComp i₂ i₁).app L.sheaf
  let n₁ := FramedNormSection.Construction.framedNormSection q₁ e.hom d z₁
  have hbase : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ n₁ ≫ AbelianModuli.HilbertConstruction.Power.PullbackComparison.powerPullbackComparison i₂ (L.pullback i₁).sheaf d =
      FramedNormSection.Construction.framedNormSection q₂ (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ e.hom) d z₂ :=
    NormSectionBaseChange.Construction.framedNormSection_baseChange q₁ q₂ j₂ i₂ hs b e.hom d z₁
  have hinput : z₂ ≫ (Scheme.Modules.pullback q₂).map c.hom = zc :=
    SquareSectionComposition.Construction.pullbackSquareSection_comp q q₁ q₂ j₁ i₁ j₂ i₂ h₁ hs.w hc z
  have hraw : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ n₁ ≫ AbelianModuli.HilbertConstruction.Power.PullbackComparison.powerPullbackComparison i₂ (L.pullback i₁).sheaf d ≫
      AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap c.hom d =
      FramedNormSection.Construction.framedNormSection q₂ (compositeNormFrame i₁ i₂ L e).hom d zc := by
    rw [← Category.assoc, hbase]
    exact (NormSectionLineIsomorphism.Construction.framedNormSection_mapIso q₂ (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ e.hom) c d z₂).symm.trans
      (congrArg (FramedNormSection.Construction.framedNormSection q₂ (compositeNormFrame i₁ i₂ L e).hom d) hinput)
  apply (cancel_mono (L.powerBaseChangeIso (i₂ ≫ i₁) d).hom).mp
  change (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ (n₁ ≫ (L.powerBaseChangeIso i₁ d).inv) ≫
      (Scheme.Modules.pullbackComp i₂ i₁).hom.app (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf d)) ≫
        AbelianModuli.HilbertConstruction.Power.PullbackComparison.powerPullbackComparison (i₂ ≫ i₁) L.sheaf d =
    (FramedNormSection.Construction.framedNormSection q₂ (compositeNormFrame i₁ i₂ L e).hom d zc ≫
      (L.powerBaseChangeIso (i₂ ≫ i₁) d).inv) ≫ (L.powerBaseChangeIso (i₂ ≫ i₁) d).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [AbelianModuli.HilbertConstruction.Power.SectionTransitions.pullbackSection_postcomp]
  simp only [Category.assoc]
  rw [← AbelianModuli.HilbertConstruction.Power.PullbackComposition.powerPullbackComparison_comp]
  change AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ n₁ ≫ (Scheme.Modules.pullback i₂).map (L.powerBaseChangeIso i₁ d).inv ≫
    (Scheme.Modules.pullback i₂).map (L.powerBaseChangeIso i₁ d).hom ≫
      AbelianModuli.HilbertConstruction.Power.PullbackComparison.powerPullbackComparison i₂ (L.pullback i₁).sheaf d ≫ AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap c.hom d = _
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id]
  erw [(Scheme.Modules.pullback i₂).map_id]
  rw [Category.id_comp]
  exact hraw

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSquareComposition.Construction
