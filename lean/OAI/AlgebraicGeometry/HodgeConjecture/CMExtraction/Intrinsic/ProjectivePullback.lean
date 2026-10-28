import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base

/-! # Projective Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectivePullback

noncomputable section

/-! Pullbacks from projective targets preserve the native Hodge structure,
using the actual Albanese comparison and its inverse. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem native_projective_pullback_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hg : D.pel.HasIntegralModelGeometry)
    (Q : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (g : D.pel.complexAlbanese.X ⟶ Q.toOver) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Mem.canonicalH1 hHodgeDecomposition Q) (Base.nativeH1 D hHodgeDecomposition hg)
      (PELModuli.IntegralModel.Product.bettiPullbackQ g 1) := by
  let P := Base.singleBaseSpacePresentation D hg
  let e := Base.nativeAlbaneseBettiEquiv D hg
  let a := (Base.singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg
  have h := ((Mem.canonicalH1 hHodgeDecomposition P).transport_isHodgeMap e.symm).comp
    (Naturality.canonicalH1_pullback hHodgeDecomposition P Q (a ≫ g))
  have he : e.symm.toLinearMap.comp (PELModuli.IntegralModel.Product.bettiPullbackQ (a ≫ g) 1) =
      PELModuli.IntegralModel.Product.bettiPullbackQ g 1 := by
    rw [PELModuli.IntegralModel.Product.bettiPullbackQ_comp]
    change e.symm.toLinearMap.comp
      ((PELModuli.IntegralModel.Product.bettiPullbackQ a 1).comp (PELModuli.IntegralModel.Product.bettiPullbackQ g 1)) = _
    rw [← Base.nativeAlbaneseBettiEquiv_eq_pullback D hg, ← LinearMap.comp_assoc]
    ext x
    exact e.symm_apply_apply _
  exact he ▸ h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectivePullback
