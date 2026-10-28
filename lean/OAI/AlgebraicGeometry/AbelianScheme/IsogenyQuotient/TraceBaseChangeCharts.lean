import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceAffineFormula

/-! # Trace Base Change Charts -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceBaseChangeCharts.Construction

noncomputable section

/-! The two global trace sections agree on every affine trace chart
lying over an original trace chart in an arbitrary Cartesian square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y X' Y' : Scheme.{u}}
  (q : X ⟶ Y) (q' : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
  [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  [IsFinite q'] [Flat q'] [LocallyOfFinitePresentation q']
  (hs : IsPullback j q' q i) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
  (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf)

set_option backward.isDefEq.respectTransparency false in
theorem finiteFlatTraceSection_baseChange_on_chart
    (U : LocalTraceSections.Construction.TraceFrameOpen q L) (V : LocalTraceSections.Construction.TraceFrameOpen q' (L.pullback i))
    (hV : V.2.openSet ≤ i ⁻¹ᵁ U.2.openSet) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.2.openSet.ι (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i (GlobalTraceSection.Construction.finiteFlatTraceSection q L z)) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.2.openSet.ι
        (GlobalTraceSection.Construction.finiteFlatTraceSection q' (L.pullback i) (SquareSectionComposition.Construction.pullbackSquareSection q q' j i hs.w z)) := by
  let W := V.2.openSet
  let Z := q' ⁻¹ᵁ W
  have hpre : Z ≤ j ⁻¹ᵁ (q ⁻¹ᵁ U.2.openSet) := by
    intro x hx
    change q (j x) ∈ U.2.openSet
    exact (congrArg (fun y => y ∈ U.2.openSet)
      (congrArg (fun f : X' ⟶ Y => f x) hs.w)).mpr (hV hx)
  let a := i.resLE U.2.openSet W hV
  let b := j.resLE (q ⁻¹ᵁ U.2.openSet) Z hpre
  have ha : a ≫ U.2.openSet.ι = W.ι ≫ i := i.resLE_comp_ι hV
  have hb : b ≫ (q ⁻¹ᵁ U.2.openSet).ι = Z.ι ≫ j := j.resLE_comp_ι hpre
  have hsmall : IsPullback b (q' ∣_ W) (q ∣_ U.2.openSet) a := by
    apply IsPullback.of_right (t := (isPullback_morphismRestrict q U.2.openSet).flip)
    · rw [ha, hb]
      exact (isPullback_morphismRestrict q' W).flip.paste_horiz hs
    · apply (cancel_mono U.2.openSet.ι).mp
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hb,
        Category.assoc, hs.w, ← Category.assoc, ← morphismRestrict_ι,
        Category.assoc, ← ha, ← Category.assoc]
  have : IsAffine W.toScheme := V.2.affine
  have : IsAffine Z.toScheme := isAffine_of_isAffineHom (q' ∣_ W)
  let c := (Scheme.Modules.pullbackComp W.ι i).app L.sheaf
  let e := V.2.frame ≪≫ c
  have hc : (Z.ι ≫ j) ≫ q = (q' ∣_ W) ≫ (W.ι ≫ i) := by
    rw [Category.assoc, hs.w, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have hleft : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (W.ι ≫ i) (GlobalTraceSection.Construction.finiteFlatTraceSection q L z) =
      TraceSquareComposition.Construction.traceSquareSection q (q' ∣_ W) (Z.ι ≫ j) (W.ι ≫ i) hc L e z := by
    have h := TraceAffineFormula.Construction.finiteFlatTraceSection_pullback_chart q L U (q' ∣_ W) b a hsmall z
    have H := congrArg (fun s => s ≫ (Scheme.Modules.pullbackCongr ha).hom.app L.sheaf) h
    rw [PullbackSectionSquares.Construction.pullbackSection_congr] at H
    exact H.trans (TraceSquareComposition.Construction.traceSquareSection_congr q (q' ∣_ W)
      (b ≫ (q ⁻¹ᵁ U.2.openSet).ι) (Z.ι ≫ j) (a ≫ U.2.openSet.ι) (W.ι ≫ i)
      _ hc hb ha L (NormSquareComposition.Construction.compositeNormFrame U.2.openSet.ι a L U.2.frame) e z)
  let z' := SquareSectionComposition.Construction.pullbackSquareSection q q' j i hs.w z
  let z₂ := SquareSectionComposition.Construction.pullbackSquareSection q' (q' ∣_ W) Z.ι W.ι (morphismRestrict_ι q' W).symm z'
  have hinput : z₂ ≫ (Scheme.Modules.pullback (q' ∣_ W)).map c.hom =
      SquareSectionComposition.Construction.pullbackSquareSection q (q' ∣_ W) (Z.ι ≫ j) (W.ι ≫ i) hc z :=
    SquareSectionComposition.Construction.pullbackSquareSection_comp q q' (q' ∣_ W) j i Z.ι W.ι hs.w
      (morphismRestrict_ι q' W).symm hc z
  have hright : LocalTraceSections.Construction.localTraceSection q' (L.pullback i) V z' ≫ c.hom =
      TraceSquareComposition.Construction.traceSquareSection q (q' ∣_ W) (Z.ι ≫ j) (W.ι ≫ i) hc L e z :=
    (FramedTraceSection.Construction.framedTraceSection_mapIso (q' ∣_ W) V.2.frame.hom c z₂).symm.trans
      (congrArg (FramedTraceSection.Construction.framedTraceSection (q' ∣_ W) e.hom) hinput)
  apply (cancel_mono c.hom).mp
  exact (PullbackSectionSquares.Construction.pullbackSection_comp W.ι i (GlobalTraceSection.Construction.finiteFlatTraceSection q L z)).trans
    (hleft.trans (hright.symm.trans (congrArg (fun s => s ≫ c.hom)
      (GlobalTraceSection.Construction.finiteFlatTraceSection_restrict q' (L.pullback i) z' V).symm)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceBaseChangeCharts.Construction
