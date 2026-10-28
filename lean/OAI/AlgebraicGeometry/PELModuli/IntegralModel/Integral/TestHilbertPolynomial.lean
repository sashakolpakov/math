import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConnectedAffineHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertPolynomialAgreement
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientFiberPolynomial

/-! # Test Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TestHilbertPolynomial

noncomputable section

/-! Every flat projective family over an integral locally noetherian
test scheme has one actual fiber Hilbert polynomial. Affine constancy
and nonempty-overlap agreement discharge the global constancy claim. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_integral_test_canonical_fiber_polynomial
    {S : Scheme.{0}} {n : ℕ} {T : Over S} [IsIntegral T.left] [IsLocallyNoetherian T.left]
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) :
    ∃ P : Polynomial ℚ, HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial (HilbertScheme.Presentations.Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P := by
  let C := T.left.affineOpenCover
  let I := {i : C.I₀ // Nonempty (Spec (C.X i))}
  let U (i : I) : Over S := Over.mk (C.f i.val ≫ T.hom)
  let f (i : I) : U i ⟶ T := Over.homMk (C.f i.val) rfl
  have : ∀ i, Nonempty (U i).left := fun i => i.property
  have : ∀ i, IsOpenImmersion (f i).left := fun i => inferInstanceAs (IsOpenImmersion (C.f i.val))
  have hcover : ∀ t : T.left, ∃ i, ∃ y : (U i).left, (f i).left y = t := by
    intro t
    obtain ⟨i, y, hy⟩ := C.openCover.exists_eq t
    exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩
  apply HilbertPolynomialAgreement.exists_fiberPolynomial_of_irreducible_open_cover U f hcover F
  intro i
  have : Nonempty (Spec (C.X i.val)) := i.property
  have : IsIntegral (Spec (C.X i.val)) := isIntegral_of_isOpenImmersion (C.f i.val)
  have : IsDomain (C.X i.val) := (affine_isIntegral_iff (C.X i.val)).mp inferInstance
  have : IsNoetherianRing (C.X i.val) := isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (C.f i.val))
  exact ConnectedAffineHilbertPolynomial.exists_connected_affine_fiber_polynomial (R := C.X i.val) (C.f i.val ≫ T.hom)
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (f i) F)

theorem exists_integral_test_fiber_polynomial
    {S : Scheme.{0}} {X T : Over S} [IsIntegral T.left] [IsLocallyNoetherian T.left]
    (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) :
    ∃ P : Polynomial ℚ, HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial BX F P := by
  obtain ⟨P, hP⟩ := exists_integral_test_canonical_fiber_polynomial
    (HilbertScheme.Presentations.Hilbert.ClosedAmbientMap.pushforwardFamily BX.closedAmbientEmbedding F)
  exact ⟨P, (HilbertScheme.Presentations.Closed.AmbientFiberPolynomial.Core.hasFiberHilbertPolynomial_closedAmbient_iff BX F P).mp hP⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.TestHilbertPolynomial
