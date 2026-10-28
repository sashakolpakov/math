import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobalFactorization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

/-! # Containment Global Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobalRepresentation.GradedHilbert

noncomputable section

/-! The actual closed native containment locus represents its entire
parameter subfunctor naturally, over every locally noetherian parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (B : Over S) [IsLocallyNoetherian B.left] (n : ℕ)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B)
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B).IdealSheafData)

theorem nativeContainmentGlobalRepresentation :
    ∃ e : yoneda.obj (ContainmentGlobal.GradedHilbert.nativeContainmentGlobalScheme B n F K) ≅
        (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).toFunctor,
      e.hom ≫ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).ι =
        yoneda.map (ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion B n F K) := by
  let j := ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion B n F K
  let : Mono j := Over.mono_of_mono_left j
  apply SubfunctorRepresentations.subfunctor_representation_of_lifts
    (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val) j
  intro T x
  constructor
  · intro hx
    exact ((ContainmentGlobalFactorization.GradedHilbert.nativeContainmentGlobal_all_tests B n F K T x).mp hx).exists
  · rintro ⟨y, hy⟩
    exact (ContainmentGlobalFactorization.GradedHilbert.nativeContainmentGlobal_all_tests B n F K T x).mpr
      ⟨y, hy, fun z hz => (cancel_mono j).mp (hz.trans hy.symm)⟩

theorem native_projective_containment_closed_locus :
    ∃ (Z : Over S) (j : Z ⟶ B), IsClosedImmersion j.left ∧
      (∀ (T : Over S) (x : T ⟶ B),
        K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x) ≤
          (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x F).val ↔
            ∃! y : T ⟶ Z, y ≫ j = x) ∧
      ∃ e : yoneda.obj Z ≅
          (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).toFunctor,
        e.hom ≫ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).ι = yoneda.map j :=
  ⟨ContainmentGlobal.GradedHilbert.nativeContainmentGlobalScheme B n F K, ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion B n F K,
    ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion_isClosedImmersion B n F K,
    ContainmentGlobalFactorization.GradedHilbert.nativeContainmentGlobal_all_tests B n F K, nativeContainmentGlobalRepresentation B n F K⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobalRepresentation.GradedHilbert
