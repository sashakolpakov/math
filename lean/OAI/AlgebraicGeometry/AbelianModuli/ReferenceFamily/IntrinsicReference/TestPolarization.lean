import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestRationalMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ToPolarizedForm

/-! # Test Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual reference-to-test comparison preserves the original
trace polarization, including its prescribed normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase

attribute [local implicit_reducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.referenceTestFiberIso Models.FinePELModel.nativeReferenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

theorem Models.FinePELModel.nativeReferenceTestFiberIso_hom :
    (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy).hom =
      (M.referenceTestFiberIso hM κ hP hκ f a y hy).polarized.abelian.hom := by
  unfold Models.FinePELModel.nativeReferenceTestFiberIso
  apply Over.OverMorphism.ext
  change (M.referenceTestFiberIso hM κ hP hκ f a y hy).polarized.abelian.hom.left ≫ 𝟙 _ = _
  exact Category.comp_id _

attribute [local irreducible] Models.FinePELModel.nativeReferenceTestRationalMarking RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm
  Intrinsic.ChernPairing.nativePolarizationForm

theorem Models.FinePELModel.nativeReferenceTestRationalMarking_polarization (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (M.complexTestFamily κ f).polarized y
      (M.nativeReferenceTestRationalMarking hM κ hP hκ f a y hy v)
      (M.nativeReferenceTestRationalMarking hM κ hP hκ f a y hy w) = P.traceForm v w := by
  let A := M.complexTestFamily κ f
  let B := A.polarized.pullback y.left
  let F := Reference.Fiber.referenceAnalyticFiber P hP a
  let R := Reference.AlgebraicModel.referenceAlgebraicModel F hP
  let D := Reference.DualModel.referenceDualModel F hP
  let p := (Reference.IsogenyKernel.referenceLatticeIsogeny_nonempty R D).some
  let C := (Reference.PicardConstruction.referencePicardConstruction_nonempty p).some
  let e := (M.referenceTestFiberIso hM κ hP hκ f a y hy).polarized
  let en := M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy
  have : IsMonHom en.hom := M.nativeReferenceTestFiberIso_group hM κ hP hκ f a y hy
  have hh := M.nativeReferenceTestFiberIso_hom hM κ hP hκ f a y hy
  have hform := Reference.ToPolarizedForm.referenceToPolarized_period_form
    (heGroup := e.abelianGroup) (hdGroup := e.dualGroup) C B e.abelian e.dual
    e.polarization e.poincare (R.nativeReferenceMarking v) (R.nativeReferenceMarking w)
  dsimp only at hform
  unfold Models.FinePELModel.nativeReferenceTestRationalMarking RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm
  change Intrinsic.ChernPairing.nativePolarizationForm B
    (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift en.hom (R.nativeReferenceMarking v))
    (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift en.hom (R.nativeReferenceMarking w)) = _
  have hmaps := @Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr R.abelian
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B))
    en.hom e.abelian.hom (M.nativeReferenceTestFiberIso_group hM κ hP hκ f a y hy) e.abelianGroup hh
  have hv := LinearMap.congr_fun hmaps (R.nativeReferenceMarking v)
  have hw := LinearMap.congr_fun hmaps (R.nativeReferenceMarking w)
  have hchern := C.chern v w
  have hmarked := hform.trans hchern
  rw [hv, hw]
  exact hmarked

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
