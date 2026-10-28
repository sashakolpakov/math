import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SchemeStalkPullback
import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Kernel
import OAI.AlgebraicGeometry.Comparison.Betti.RingKernelEquivTransport

/-! # Scheme Stalk Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.SchemeStalkNormalization

noncomputable section

/-! The actual ring-category algebraic stalk pullback is the original scheme stalk map, including its localized defining ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

theorem algebraicSchemeStalkPullback_normalization
    (a : Analytification.RingedStalk.algebraicRingCatStalk Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) :
    CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Analytification.Base.analytificationMap X p)
      (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p a) =
    f.left.stalkMap (Analytification.Base.analytificationMap X p)
      (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv Y.left.presheaf
        (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) a) := by
  obtain ⟨U, hpU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := RingCat)
    (X := TopCat.of Y.left) Y.left.ringCatSheaf.obj a
  dsimp only [Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback]
  erw [Module.RingedStalkPushforward.Local.ringedStalkMap_germ, CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv_germ,
    CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv_germ]
  exact (f.left.germ_stalkMap_apply U (Analytification.Base.analytificationMap X p) hpU s).symm

theorem algebraicSchemeStalkPullback_surjective [IsClosedImmersion f.left] :
    Function.Surjective (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p) := by
  let eS := CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv Y.left.presheaf
    (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))
  let eT := CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Analytification.Base.analytificationMap X p)
  intro b
  obtain ⟨a, ha⟩ := f.left.stalkMap_surjective (Analytification.Base.analytificationMap X p) (eT b)
  refine ⟨eS.symm a, eT.injective ?_⟩
  exact (algebraicSchemeStalkPullback_normalization f p (eS.symm a)).trans
    ((congrArg (f.left.stalkMap (Analytification.Base.analytificationMap X p)) (eS.apply_symm_apply a)).trans ha)

theorem algebraicSchemeStalkPullback_ker [IsClosedImmersion f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (hpU : Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) ∈ U) :
    RingHom.ker (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p) =
      Ideal.map (TopCat.Presheaf.germ (C := RingCat) (X := TopCat.of Y.left)
        Y.left.ringCatSheaf.obj U
        (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) hpU).hom
        (RingHom.ker (f.left.app U).hom) := by
  apply RingKernelEquivTransport.ringKernel_eq_map_of_equiv_square (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)
    (f.left.stalkMap (Analytification.Base.analytificationMap X p)).hom
    (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv Y.left.presheaf
      (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)))
    (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Analytification.Base.analytificationMap X p))
    (algebraicSchemeStalkPullback_normalization f p) _
    (Y.left.presheaf.germ U (f.left (Analytification.Base.analytificationMap X p)) hpU).hom
  · apply RingHom.ext
    exact CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv_germ Y.left.presheaf _ U hpU
  · exact ClosedImmersion.Kernel.closedImmersion_stalkMap_ker f.left U hU (Analytification.Base.analytificationMap X p) hpU

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.SchemeStalkNormalization
