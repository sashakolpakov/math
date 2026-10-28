import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernClassOperations
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed

/-! # Biextension Chern Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity

noncomputable section

/-! The actual Poincare tensor identity gives the difference between
the multiplication pullback and the two projection pullbacks of the
native Chern class, on the genuine Segre-presented scheme product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def nativeChernPullback {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : Y.toOver ⟶ X.toOver) :
    X.rationalCohomology 2 →ₗ[ℚ] Y.rationalCohomology 2 :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 2).hom

theorem lineBundleChernClass_biextension (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (B : HilbertConstruction.Line.Bundles.LineBundle (A.toOver ⊗ A.toOver).left)
    (e : ((B.tensor (L.pullback (fst A.toOver A.toOver).left)).tensor
      (L.pullback (snd A.toOver A.toOver).left)).sheaf ≅ (L.pullback (MonObj.mul (X := A.toOver)).left).sheaf) :
    Intrinsic.ChernClasses.lineBundleChernClass (Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation A.variety.presentation) B =
      nativeChernPullback (X := A.variety.presentation)
        (Y := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation A.variety.presentation)
        (MonObj.mul (X := A.toOver)) (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L) -
      nativeChernPullback (X := A.variety.presentation)
        (Y := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation A.variety.presentation)
        (fst A.toOver A.toOver) (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L) -
      nativeChernPullback (X := A.variety.presentation)
        (Y := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation A.variety.presentation)
        (snd A.toOver A.toOver) (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L) := by
  let X := A.variety.presentation
  let Z := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation X X
  have h := Intrinsic.ChernClasses.lineBundleChernClass_iso Z
    ((B.tensor (L.pullback (fst A.toOver A.toOver).left)).tensor (L.pullback (snd A.toOver A.toOver).left))
    (L.pullback (MonObj.mul (X := A.toOver)).left) e
  rw [ChernTensorAdditivity.lineBundleChernClass_tensor, ChernTensorAdditivity.lineBundleChernClass_tensor,
    ChernEmbeddingIndependence.lineBundleChernClass_pullback (X := X) (Y := Z) (fst A.toOver A.toOver) L,
    ChernEmbeddingIndependence.lineBundleChernClass_pullback (X := X) (Y := Z) (snd A.toOver A.toOver) L,
    ChernEmbeddingIndependence.lineBundleChernClass_pullback (X := X) (Y := Z) (MonObj.mul (X := A.toOver)) L] at h
  exact (eq_sub_iff_add_eq).mpr ((eq_sub_iff_add_eq).mpr ((add_right_comm _ _ _).trans h))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity
