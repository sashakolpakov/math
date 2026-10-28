import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart

/-! # Translation Frame Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TranslationFrameCoefficients.Construction

noncomputable section

/-! Original difference-frame transitions are the quotient of the
original ambient pullbacks. On an actual affine translation chart their
first-order coefficient is the constant-conormal unit logarithm. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem transported_ratio {M N : Type*} [CommGroup M] [CommGroup N]
    (r : M →* N) (u x y : M) (a b : N)
    (hu : u = x / y) (hx : r x = a) (hy : r y = b) : r u = a / b := by
  rw [hu, map_div, hx, hy]

private theorem normalize_unit_equiv {A B V : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (f : Bˣ → V) (g : Aˣ → V)
    (h : ∀ u, f (Units.map e.toMonoidHom u) = g u) (u : Bˣ) :
    f u = g (Units.map e.symm.toMonoidHom u) := by
  have hu : Units.map e.toMonoidHom (Units.map e.symm.toMonoidHom u) = u :=
    Units.ext (e.apply_symm_apply u.val)
  exact (congrArg f hu).symm.trans (h (Units.map e.symm.toMonoidHom u))

theorem differenceFrame_transition_sections
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {Y : Scheme.{0}}
    (f g : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (h : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ f =
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf)
    (W : Y.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L s).transition (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L t)
      (g ⁻¹ᵁ W) (g.preimage_mono hs) (g.preimage_mono ht) =
      Units.map (f.appLE W (g ⁻¹ᵁ W) (AbelianModuli.ReferenceFamily.EqualReductionOpenSquares.equalDualReduction_preimage X f g h W).ge).hom.toMonoidHom
        (s.transition t W hs ht) /
      Units.map (g.appLE W (g ⁻¹ᵁ W) le_rfl).hom.toMonoidHom (s.transition t W hs ht) := by
  have hg : (g ∣_ W) = g.resLE W (g ⁻¹ᵁ W) le_rfl := by
    apply (cancel_mono W.ι).mp
    rw [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι]
  rw [AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame_transition, AbelianModuli.ReferenceFamily.EqualReductionOpenSquares.equalDualReductionOpenMap,
    AbelianModuli.ReferenceFamily.Open.UnitCoordinates.openUnitToRegular_resLE, AbelianModuli.ReferenceFamily.Open.UnitCoordinates.openUnitToRegular_toOpen, hg,
    AbelianModuli.ReferenceFamily.Open.UnitCoordinates.openUnitToRegular_resLE, AbelianModuli.ReferenceFamily.Open.UnitCoordinates.openUnitToRegular_toOpen]

theorem regularUnitTransport_appLE {X Y : Scheme.{0}} (f : X ⟶ Y)
    (U : Y.Opens) {V V' : X.Opens} (hV : V = V')
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hV).toMonoidHom
      (Units.map (f.appLE U V h).hom.toMonoidHom u) =
      Units.map (f.appLE U V' h').hom.toMonoidHom u :=
  Units.ext (AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism.regularSectionTransport_appLE f rfl hV h h' u.val)

private theorem differenceFrame_transition_transport
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {Y : Scheme.{0}}
    (f g : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (h : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ f =
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf)
    (W : Y.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain)
    (V : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hV : g ⁻¹ᵁ W = V)
    (hf : V ≤ f ⁻¹ᵁ W) (hg : V ≤ g ⁻¹ᵁ W) :
    Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hV).toMonoidHom
      ((AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L s).transition
        (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame X f g h L t) (g ⁻¹ᵁ W)
        (g.preimage_mono hs) (g.preimage_mono ht)) =
      Units.map (f.appLE W V hf).hom.toMonoidHom (s.transition t W hs ht) /
        Units.map (g.appLE W V hg).hom.toMonoidHom (s.transition t W hs ht) := by
  exact transported_ratio (Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hV).toMonoidHom)
    _ _ _ _ _ (differenceFrame_transition_sections X f g h L s t W hs ht)
    (regularUnitTransport_appLE f W hV (AbelianModuli.ReferenceFamily.EqualReductionOpenSquares.equalDualReduction_preimage X f g h W).ge
      hf (s.transition t W hs ht))
    (regularUnitTransport_appLE g W hV le_rfl hg (s.transition t W hs ht))

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle G.left) (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf)

def translatedFrameTransition (v : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints G 1)
    (W : G.left.Opens) (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left, (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ W)ˣ :=
  (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G v).left
    (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G v) L s).transition
      (AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames.dualDifferenceOpenFrame G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G v).left
        (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G v) L t)
      ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ W)
      ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.preimage_mono hs)
      ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.preimage_mono ht)

private theorem translatedFrameTransition_transport_general
    (w : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints G 1) (W : G.left.Opens)
    (hs : W ≤ s.domain) (ht : W ≤ t.domain)
    (V : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left.Opens)
    (hV : (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ W = V)
    (hf : V ≤ (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G w).left ⁻¹ᵁ W)
    (hg : V ≤ (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ W) :
    Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport hV).toMonoidHom
      (translatedFrameTransition G L s t w W hs ht) =
    Units.map ((AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G w).left.appLE W V hf).hom.toMonoidHom
      (s.transition t W hs ht) /
    Units.map ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.appLE W V hg).hom.toMonoidHom
      (s.transition t W hs ht) :=
  differenceFrame_transition_transport G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G w).left
    (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G w)
    L s t W hs ht V hV hf hg

variable [IsIntegral G.left] [Smooth G.hom]
    (B : CommAlgCat ℂ) (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion i.left]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension G.hom) → ℂ)
    (hs : i.left.opensRange ≤ s.domain) (ht : i.left.opensRange ≤ t.domain)

private def nativeRatioCoefficient (u : Γ(G.left, i.left.opensRange)ˣ) : B :=
  (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm.toMonoidHom
    (Units.map ((AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)).left.appLE
      i.left.opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
      (AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits.nativeTranslationOpenRange_le G B i v)).hom.toMonoidHom u /
     Units.map ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.appLE i.left.opensRange
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
      (AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits.nativeProjectionOpenRange_le G B i)).hom.toMonoidHom u)).val.snd

private theorem nativeRatioCoefficient_map (u : Bˣ) :
    nativeRatioCoefficient G B i v
      (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i).toMonoidHom u) =
      AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm
        (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v))) u :=
  AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits.nativeTranslationOpenUnitRatio_coefficient G B i v u

private theorem nativeRatioCoefficient_section (u : Γ(G.left, i.left.opensRange)ˣ) :
    nativeRatioCoefficient G B i v u =
      AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm
        (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v)))
        (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i).symm.toMonoidHom u) :=
  normalize_unit_equiv (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i)
    (nativeRatioCoefficient G B i v)
    (AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm
      (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v))))
    (nativeRatioCoefficient_map G B i v) u

private theorem translatedFrameTransition_transport :
    Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).symm).toMonoidHom
      (translatedFrameTransition G L s t (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)
        i.left.opensRange hs ht) =
    Units.map ((AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)).left.appLE
      i.left.opensRange (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
      (AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits.nativeTranslationOpenRange_le G B i v)).hom.toMonoidHom
        (s.transition t i.left.opensRange hs ht) /
    Units.map ((snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left.appLE i.left.opensRange
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
      (AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits.nativeProjectionOpenRange_le G B i)).hom.toMonoidHom
        (s.transition t i.left.opensRange hs ht) :=
  translatedFrameTransition_transport_general G L s t
    (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v) i.left.opensRange hs ht
    (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
    (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).symm
    (AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits.nativeTranslationOpenRange_le G B i v) (AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits.nativeProjectionOpenRange_le G B i)

/-- The coefficient of the actual difference-frame transition, after
the proved identification of its open with the original affine chart,
is exactly the logarithmic derivative of the original transition unit. -/
theorem translatedFrameTransition_nativeCoefficient :
    let e := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)
    let e₀ := AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i
    (Units.map e.symm.toMonoidHom
      (Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart.dualAffineTranslationChart_range G B i).symm).toMonoidHom
        (translatedFrameTransition G L s t (AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)
          i.left.opensRange hs ht))).val.snd =
      AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm
        (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B (AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v)))
        (Units.map e₀.symm.toMonoidHom (s.transition t i.left.opensRange hs ht)) := by
  exact (congrArg (fun u : Γ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G).left,
      (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange)ˣ =>
      (Units.map (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
        (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ G) (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm.toMonoidHom u).val.snd)
    (translatedFrameTransition_transport G L s t B i v hs ht)).trans
      (nativeRatioCoefficient_section G B i v (s.transition t i.left.opensRange hs ht))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TranslationFrameCoefficients.Construction
