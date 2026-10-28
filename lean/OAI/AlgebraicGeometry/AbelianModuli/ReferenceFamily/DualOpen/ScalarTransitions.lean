import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StableOpenFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Scalars

/-! # Scalar Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.ScalarTransitions

noncomputable section

/-! Actual scalar pullback of arbitrary local pullback frames has
the scalar-pulled original regular transition units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualOpenScalar_restrict (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {U W : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens}
    (h : W ≤ U) (c : ℂ) :
    Scalars.dualOpenScalar X W c ≫ (LieRanks.dualNumberTest ℂ ⊗ X).left.homOfLE h =
      (LieRanks.dualNumberTest ℂ ⊗ X).left.homOfLE h ≫ Scalars.dualOpenScalar X U c := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, Scalars.dualOpenScalar_ι, Category.assoc, Scalars.dualOpenScalar_ι,
    ← Category.assoc, Scheme.homOfLE_ι]

theorem dualScalarPullbackFrame_transition (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (M : (LieRanks.dualNumberTest ℂ ⊗ X).left.Modules)
    (U V W : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : W ≤ U) (hV : W ≤ V) (c : ℂ)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback V.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme) :
    (Dual.TensorCechCoefficients.localFrameFromPullback U (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (Dual.Scalars.dualFamilyScalar X c).left U.ι U.ι
      (Scalars.dualOpenScalar X U c) (Scalars.dualOpenScalar_ι X U c) M e)).transition
      (Dual.TensorCechCoefficients.localFrameFromPullback V (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (Dual.Scalars.dualFamilyScalar X c).left V.ι V.ι
        (Scalars.dualOpenScalar X V c) (Scalars.dualOpenScalar_ι X V c) M d)) W hU hV =
    Units.map (Scalars.dualOpenScalarSection X W c).toMonoidHom
      ((Dual.TensorCechCoefficients.localFrameFromPullback U e).transition (Dual.TensorCechCoefficients.localFrameFromPullback V d) W hU hV) :=
  StableOpenFrameTransitions.stableOpenFrame_transition (Dual.Scalars.dualFamilyScalar X c).left M U V W hU hV
    (Scalars.dualOpenScalar X U c) (Scalars.dualOpenScalar X V c) (Scalars.dualOpenScalar X W c)
    (Scalars.dualOpenScalar_ι X U c) (Scalars.dualOpenScalar_ι X V c) (Scalars.dualOpenScalar_ι X W c)
    (dualOpenScalar_restrict X hU c) (dualOpenScalar_restrict X hV c) e d

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.ScalarTransitions
