import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductPoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossClassEvaluation

/-! # Product Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductCohomology

noncomputable section

/-! The native scheme-product comparison respects the actual singular
pullbacks of multiplication and of both projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem singularCohomology_comp_apply {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Z n) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g n c) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (f ≫ g) n c :=
  (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ) f g n) c).symm

theorem singularCohomology_commuting_square {W X Y Z : TopCat.{0}}
    (a : W ⟶ X) (b : X ⟶ Z) (c : W ⟶ Y) (d : Y ⟶ Z) (h : a ≫ b = c ≫ d)
    (n : ℕ) (z : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Z n) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) a n
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) b n z) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) c n
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) d n z) :=
  (singularCohomology_comp_apply a b n z).trans
    ((congrArg (fun f => AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n z) h).trans
      (singularCohomology_comp_apply c d n z).symm)

def nativeProductCohomologyPullback (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    (Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation B.variety.presentation).rationalCohomology 2 →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Betti.Scheme.schemePointSpace A.toOver × Betti.Scheme.schemePointSpace B.toOver)) 2 :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (ProductPoints.nativeProductPointMap A B) 2).hom

theorem nativeProductCohomologyPullback_map (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : A.toOver ⊗ B.toOver ⟶ X.toOver) (c : X.rationalCohomology 2) :
    nativeProductCohomologyPullback A B
      (BiextensionChernIdentity.nativeChernPullback (X := X)
        (Y := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation B.variety.presentation) f c) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (ProductPoints.nativeProductPointMap A B ≫ TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 2 c :=
  singularCohomology_comp_apply (ProductPoints.nativeProductPointMap A B)
    (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 2 c

theorem nativeProductCohomologyPullback_mul (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (c : A.variety.presentation.rationalCohomology 2) :
    nativeProductCohomologyPullback A A
      (BiextensionChernIdentity.nativeChernPullback (X := A.variety.presentation)
        (Y := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation A.variety.presentation)
        (MonObj.mul (X := A.toOver)) c) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (ChernPairing.nativeMultiplication A) 2 c := by
  have h := nativeProductCohomologyPullback_map A A (MonObj.mul (X := A.toOver)) c
  rw [ProductPoints.nativeProductPointMap_mul] at h
  exact h

theorem nativeProductCohomologyPullback_fst (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : A.variety.presentation.rationalCohomology 2) :
    nativeProductCohomologyPullback A B
      (BiextensionChernIdentity.nativeChernPullback (X := A.variety.presentation)
        (Y := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation B.variety.presentation)
        (fst A.toOver B.toOver) c) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst 2 c := by
  have h := nativeProductCohomologyPullback_map A B (fst A.toOver B.toOver) c
  rw [ProductPoints.nativeProductPointMap_fst] at h
  exact h

theorem nativeProductCohomologyPullback_snd (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : B.variety.presentation.rationalCohomology 2) :
    nativeProductCohomologyPullback A B
      (BiextensionChernIdentity.nativeChernPullback (X := B.variety.presentation)
        (Y := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation B.variety.presentation)
        (snd A.toOver B.toOver) c) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd 2 c := by
  have h := nativeProductCohomologyPullback_map A B (snd A.toOver B.toOver) c
  rw [ProductPoints.nativeProductPointMap_snd] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductCohomology
