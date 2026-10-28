import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquareFrameTransitionRecovery

/-! # Restricted Square Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedSquareFrameTransitions

noncomputable section

/-! Actual frames pulled to compatible source opens have transition
units given by the original ambient scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem schemeResLE_restriction_square {X Y : Scheme.{0}} (f : X ⟶ Y)
    {U W : Y.Opens} {V Z : X.Opens} (hU : W ≤ U) (hV : Z ≤ V)
    (h : V ≤ f ⁻¹ᵁ U) (h' : Z ≤ f ⁻¹ᵁ W) :
    f.resLE W Z h' ≫ Y.homOfLE hU = X.homOfLE hV ≫ f.resLE U V h := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι,
    Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]

theorem restrictedSquareFrame_transition {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (U V W : Y.Opens) (U' V' W' : X.Opens)
    (hU : W ≤ U) (hV : W ≤ V) (hU' : W' ≤ U') (hV' : W' ≤ V')
    (pU : U' ≤ f ⁻¹ᵁ U) (pV : V' ≤ f ⁻¹ᵁ V) (pW : W' ≤ f ⁻¹ᵁ W)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback V.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme) :
    (Dual.TensorCechCoefficients.localFrameFromPullback U' (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f U'.ι U.ι (f.resLE U U' pU)
      (Scheme.Hom.resLE_comp_ι f pU) M e)).transition
      (Dual.TensorCechCoefficients.localFrameFromPullback V' (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f V'.ι V.ι (f.resLE V V' pV)
        (Scheme.Hom.resLE_comp_ι f pV) M d)) W' hU' hV' =
      Units.map (f.appLE W W' pW).hom.toMonoidHom
        ((Dual.TensorCechCoefficients.localFrameFromPullback U e).transition (Dual.TensorCechCoefficients.localFrameFromPullback V d) W hU hV) := by
  have H := SquareFrameTransitionRecovery.squarePulledFrame_transition f M U V W U' V' W' hU hV hU' hV'
    (f.resLE U U' pU) (f.resLE V V' pV) (f.resLE W W' pW)
    (Scheme.Hom.resLE_comp_ι f pU) (Scheme.Hom.resLE_comp_ι f pV) (Scheme.Hom.resLE_comp_ι f pW)
    (schemeResLE_restriction_square f hU hU' pU pW)
    (schemeResLE_restriction_square f hV hV' pV pW) e d
  exact H.trans ((Open.UnitCoordinates.openUnitToRegular_resLE f W W' pW _).trans
    (congrArg (Units.map (f.appLE W W' pW).hom.toMonoidHom) (Open.UnitCoordinates.openUnitToRegular_toOpen W _)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedSquareFrameTransitions
