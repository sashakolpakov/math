import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalTraceSection

/-! # Trace Affine Formula -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceAffineFormula.Construction

noncomputable section

/-! The glued trace recovers the finite-free affine formula and can
be pulled back through any affine Cartesian square over a trace chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
variable {X Y : Scheme.{u}} (q : X ⟶ Y)
  [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)

set_option backward.isDefEq.respectTransparency false in
theorem finiteFlatTraceSection_eq_framed [IsAffine X] [IsAffine Y]
    {ι : Type v} [Fintype ι]
    (b : letI := q.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ L.sheaf)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    GlobalTraceSection.Construction.finiteFlatTraceSection q L z = FramedTraceSection.Construction.framedTraceSection q e.hom z := by
  apply ((GlobalTraceSection.Construction.existsUnique_globalTraceSection q L z).choose_spec.2 _ ?_).symm
  intro U
  have : IsAffine U.2.openSet.toScheme := U.2.affine
  have : IsAffine (q ⁻¹ᵁ U.2.openSet).toScheme := isAffine_of_isAffineHom (q ∣_ U.2.openSet)
  have : IsIso U.2.frame.hom := U.2.frame.isIso_hom
  exact (FramedTraceBaseChange.Construction.framedTraceSection_baseChange q (q ∣_ U.2.openSet) (q ⁻¹ᵁ U.2.openSet).ι
    U.2.openSet.ι (isPullback_morphismRestrict q U.2.openSet).flip b e.hom z).trans
    (FramedTraceSection.Construction.framedTraceSection_frame_independent (L := (L.pullback U.2.openSet.ι).sheaf) (q ∣_ U.2.openSet)
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.2.openSet.ι e.hom) U.2.frame.hom _)

set_option backward.isDefEq.respectTransparency false in
theorem finiteFlatTraceSection_pullback_chart
    (U : LocalTraceSections.Construction.TraceFrameOpen q L) {X' Y' : Scheme.{u}} [IsAffine X'] [IsAffine Y']
    (g : X' ⟶ Y') (j : X' ⟶ (q ⁻¹ᵁ U.2.openSet).toScheme)
    (i : Y' ⟶ U.2.openSet.toScheme) (hs : IsPullback j g (q ∣_ U.2.openSet) i)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (i ≫ U.2.openSet.ι) (GlobalTraceSection.Construction.finiteFlatTraceSection q L z) =
      TraceSquareComposition.Construction.traceSquareSection q g (j ≫ (q ⁻¹ᵁ U.2.openSet).ι) (i ≫ U.2.openSet.ι)
        (by rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hs.w, Category.assoc])
        L (NormSquareComposition.Construction.compositeNormFrame U.2.openSet.ι i L U.2.frame) z := by
  have : IsAffine U.2.openSet.toScheme := U.2.affine
  have : IsAffine (q ⁻¹ᵁ U.2.openSet).toScheme := isAffine_of_isAffineHom (q ∣_ U.2.openSet)
  rw [← PullbackSectionSquares.Construction.pullbackSection_comp i U.2.openSet.ι, GlobalTraceSection.Construction.finiteFlatTraceSection_restrict]
  exact TraceSquareComposition.Construction.traceSquareSection_comp q (q ∣_ U.2.openSet) g
    (q ⁻¹ᵁ U.2.openSet).ι U.2.openSet.ι j i
    (morphismRestrict_ι q U.2.openSet).symm hs _ U.2.basis L U.2.frame z

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceAffineFormula.Construction
