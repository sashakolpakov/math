import OAI.RepresentationTheory.Theta.Geometric.LinePeriodPairing
import OAI.RepresentationTheory.Theta.Geometric.Reference.ChernAdjoint

/-! # Poincare Detection -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference

noncomputable section

/-! The original theta Poincare class separates dual periods and
detects actual group maps into the constructed dual abelian variety. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} (C : PolarizationConstruction.ReferencePolarizationConstruction p)

def PolarizationConstruction.ReferencePolarizationConstruction.periodPairing : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods N.abelian →ₗ[ℚ] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian →ₗ[ℚ] ℚ :=
  LinePeriodPairing.linePeriodPairing N.abelian M.abelian (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)

theorem PolarizationConstruction.ReferencePolarizationConstruction.periodPairing_isogeny (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ N.abelian.toOver from p.isogeny.hom) x) y =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  let f : M.abelian.toOver ⟶ N.abelian.toOver := p.isogeny.hom
  have hp := LinePeriodPairing.linePeriodPairing_pullback M.abelian M.abelian N.abelian M.abelian f (𝟙 M.abelian.toOver)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) x y
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id] at hp
  have he := LinePeriodPairing.linePeriodPairing_biextension M.abelian C.ampleLine
    (C.poincare.pullback (f ⊗ₘ 𝟙 M.abelian.toOver).left)
    (QuotientDifferenceFibers.quotientDifference_formulaIso p.isogeny C.ampleLine C.poincare C.difference)
  exact hp.symm.trans (LinearMap.congr_fun (LinearMap.congr_fun he x) y)

theorem PolarizationConstruction.ReferencePolarizationConstruction.periodPairing_left_ext (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods N.abelian)
    (h : ∀ w, C.periodPairing x w = C.periodPairing y w) : x = y := by
  obtain ⟨u, rfl⟩ := (PolarizationConstruction.ReferencePolarizationConstruction.latticeIsogeny_period_bijective (p := p)).surjective x
  obtain ⟨v, rfl⟩ := (PolarizationConstruction.ReferencePolarizationConstruction.latticeIsogeny_period_bijective (p := p)).surjective y
  apply congrArg (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ N.abelian.toOver from p.isogeny.hom))
  apply C.chernForm_left_ext
  intro w
  exact (C.periodPairing_isogeny u w).symm.trans ((h w).trans (C.periodPairing_isogeny v w))

theorem PolarizationConstruction.ReferencePolarizationConstruction.periodPairing_detects_group_maps (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f g : A.toOver ⟶ N.abelian.toOver) [IsMonHom f] [IsMonHom g]
    (h : ∀ x y, C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) y = C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g x) y) : f = g := by
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful f g
  apply LinearMap.ext
  intro x
  exact C.periodPairing_left_ext _ _ (h x)

end

end OAI.RepresentationTheory.Theta.Geometric.Reference
