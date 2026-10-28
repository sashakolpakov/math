import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.SchemeStalkNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.HolomorphicStalk

/-! # Stalk Kernel -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.StalkKernel

noncomputable section

/-! The kernel of the actual holomorphic stalk pullback is the extension of the kernel of the actual algebraic stalk pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]

theorem closedImmersion_analyticStalk_kernel (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    RingHom.ker (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p) =
      Ideal.map (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))
        (RingHom.ker (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)) := by
  obtain ⟨U, hU, hpU, hker⟩ := HolomorphicStalk.analyticHolomorphicStalkPullback_exists_affine_kernel f p
  let I := RingHom.ker (f.left.app U).hom
  let u : Γ(Y.left, U) →+* Analytification.RingedStalk.algebraicRingCatStalk Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) :=
    (TopCat.Presheaf.germ (C := RingCat) (X := TopCat.of Y.left)
      Y.left.ringCatSheaf.obj U
      (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) hpU).hom
  let v := (Y.left.presheaf.germ U
    (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) hpU).hom
  let a := Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
  let b := ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
  have hg : a.comp u = b.comp v := by
    apply RingHom.ext
    intro s
    have hn := RingHom.congr_fun
      (Analytification.RingedStalk.analytificationRingedStalkMap_eq Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) (u s)
    change a (u s) = b
      (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv Y.left.presheaf
        (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) (u s)) at hn
    exact hn.trans (congrArg b
      (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv_germ Y.left.presheaf _ U hpU s))
  calc
    RingHom.ker (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p) = Ideal.map (b.comp v) I := hker
    _ = Ideal.map (a.comp u) I := congrArg (fun k : Γ(Y.left, U) →+*
        ConcreteHolomorphicStalkMap.analyticHolomorphicStalk Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) => Ideal.map k I) hg.symm
    _ = Ideal.map a (Ideal.map u I) := (Ideal.map_map u a).symm
    _ = Ideal.map a (RingHom.ker (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)) :=
      congrArg (Ideal.map a) (Algebraic.SchemeStalkNormalization.algebraicSchemeStalkPullback_ker f p U hU hpU).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.StalkKernel
