import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedTraceBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSquareComposition

/-! # Trace Square Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceSquareComposition.Construction

noncomputable section

/-! Trace sections agree under successive base changes, including
the canonical comparison between iterated and composite pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def traceSquareSection {X Y X' Y' : Scheme.{u}}
    (q : X ⟶ Y) (q' : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (h : j ≫ q = q' ≫ i) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' ≅ (L.pullback i).sheaf)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' ⟶ (L.pullback i).sheaf :=
  FramedTraceSection.Construction.framedTraceSection q' e.hom (SquareSectionComposition.Construction.pullbackSquareSection q q' j i h z)

set_option backward.isDefEq.respectTransparency false in
theorem traceSquareSection_comp
    {X Y X₁ Y₁ X₂ Y₂ : Scheme.{u}}
    [IsAffine X₁] [IsAffine Y₁] [IsAffine X₂] [IsAffine Y₂]
    (q : X ⟶ Y) (q₁ : X₁ ⟶ Y₁) (q₂ : X₂ ⟶ Y₂)
    (j₁ : X₁ ⟶ X) (i₁ : Y₁ ⟶ Y) (j₂ : X₂ ⟶ X₁) (i₂ : Y₂ ⟶ Y₁)
    (h₁ : j₁ ≫ q = q₁ ≫ i₁) (hs : IsPullback j₂ q₂ q₁ i₂)
    (hc : (j₂ ≫ j₁) ≫ q = q₂ ≫ (i₂ ≫ i₁))
    {ι : Type v} [Fintype ι]
    (b : letI := q₁.appTop.hom.toAlgebra; Module.Basis ι Γ(Y₁, ⊤) Γ(X₁, ⊤))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y₁ ≅ (L.pullback i₁).sheaf)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ (traceSquareSection q q₁ j₁ i₁ h₁ L e z) ≫
        (Scheme.Modules.pullbackComp i₂ i₁).hom.app L.sheaf =
      traceSquareSection q q₂ (j₂ ≫ j₁) (i₂ ≫ i₁) hc L
        (NormSquareComposition.Construction.compositeNormFrame i₁ i₂ L e) z := by
  let z₁ := SquareSectionComposition.Construction.pullbackSquareSection q q₁ j₁ i₁ h₁ z
  let z₂ := SquareSectionComposition.Construction.pullbackSquareSection q₁ q₂ j₂ i₂ hs.w z₁
  let zc := SquareSectionComposition.Construction.pullbackSquareSection q q₂ (j₂ ≫ j₁) (i₂ ≫ i₁) hc z
  let c := (Scheme.Modules.pullbackComp i₂ i₁).app L.sheaf
  have hbase : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ (FramedTraceSection.Construction.framedTraceSection q₁ e.hom z₁) =
      FramedTraceSection.Construction.framedTraceSection q₂ (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ e.hom) z₂ :=
    FramedTraceBaseChange.Construction.framedTraceSection_baseChange q₁ q₂ j₂ i₂ hs b e.hom z₁
  have hinput : z₂ ≫ (Scheme.Modules.pullback q₂).map c.hom = zc :=
    SquareSectionComposition.Construction.pullbackSquareSection_comp q q₁ q₂ j₁ i₁ j₂ i₂ h₁ hs.w hc z
  change AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ (FramedTraceSection.Construction.framedTraceSection q₁ e.hom z₁) ≫ c.hom = _
  rw [hbase]
  exact (FramedTraceSection.Construction.framedTraceSection_mapIso q₂ (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i₂ e.hom) c z₂).symm.trans
    (congrArg (FramedTraceSection.Construction.framedTraceSection q₂ (NormSquareComposition.Construction.compositeNormFrame i₁ i₂ L e).hom) hinput)

set_option backward.isDefEq.respectTransparency false in
theorem traceSquareSection_congr {X Y X' Y' : Scheme.{u}}
    (q : X ⟶ Y) (q' : X' ⟶ Y') (j j' : X' ⟶ X) (i i' : Y' ⟶ Y)
    (h : j ≫ q = q' ≫ i) (h' : j' ≫ q = q' ≫ i') (hj : j = j') (hi : i = i')
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' ≅ (L.pullback i).sheaf)
    (e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y' ≅ (L.pullback i').sheaf)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    traceSquareSection q q' j i h L e z ≫
        (Scheme.Modules.pullbackCongr hi).hom.app L.sheaf =
      traceSquareSection q q' j' i' h' L e' z := by
  subst j'
  subst i'
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app]
  exact FramedTraceSection.Construction.framedTraceSection_frame_independent q' e.hom e'.hom _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceSquareComposition.Construction
