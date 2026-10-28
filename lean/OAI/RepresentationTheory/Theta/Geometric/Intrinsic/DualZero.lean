import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.MapFirstJet
import OAI.RepresentationTheory.Theta.Geometric.Dual.AffineBaseChangeChart

/-! # Dual Zero -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualZero

noncomputable section

/-! The zero native tangent is the actual constant dual-number point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold

theorem nativeAffineDualPoint_zero {A : Type*} [CommRing A] [Algebra ℂ A]
    [IsDomain A] [Algebra.Smooth ℂ A] (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x 0).val = (Algebra.ofId ℂ (DualNumber ℂ)).comp x := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints.nativeAffineDualPoint_fst x 0 a
  · change ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints.nativeAffineDualPointEquiv x 0).val a).snd = 0
    exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.AffineDualPoints.nativeAffineDualPoint_snd x 0 a).trans (map_zero _)

set_option backward.isDefEq.respectTransparency false in
theorem nativeSchemeTangentDual_zero (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p 0).val = toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ p := by
  obtain ⟨A, hAd, hAs, i, hi, x, hx⟩ := AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality.exists_smoothAffineOpenPoint_lift X p
  let : IsDomain A := hAd
  let : Algebra.Smooth ℂ A := hAs
  let : IsOpenImmersion i.left := hi
  have H := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDual_mfderiv X A i x 0
  rw [map_zero, hx, nativeAffineDualPoint_zero] at H
  have ha : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualOpen.affineDualSchemeMap ((Algebra.ofId ℂ (DualNumber ℂ)).comp x) =
      toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A x := by
    apply Over.OverMorphism.ext
    exact Spec.map_comp (CommRingCat.ofHom x.toRingHom)
      (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))
  rw [ha, Category.assoc] at H
  exact H.trans (congrArg (fun q => toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ q) hx)

set_option backward.isDefEq.respectTransparency false in
theorem nativeMapFirstJet_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : V) :
    MapFirstJet.nativeMapFirstJet X p z 0 = toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ p z := by
  unfold MapFirstJet.nativeMapFirstJet
  rw [map_zero]
  exact nativeSchemeTangentDual_zero X (p z)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualZero
