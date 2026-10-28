import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ChernAdjoint
import OAI.RepresentationTheory.Theta.Geometric.LinePeriodPairing

/-! # Poincare Period Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual constructed Poincare bundle pairs dual periods
nondegenerately and detects algebraic group maps into the dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.LinePeriodPairing

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} (C : PicardConstruction.ReferencePicardConstruction p)

def PicardConstruction.ReferencePicardConstruction.periodPairing : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian →ₗ[ℚ] ℚ :=
  RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing D.abelian M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)

theorem PicardConstruction.ReferencePicardConstruction.periodPairing_isogeny (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    C.periodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom) x) y =
      Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  let f : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  let : IsMonHom f := inferInstanceAs (IsMonHom p.isogeny.hom)
  have hp := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback M.abelian M.abelian D.abelian M.abelian f (𝟙 M.abelian.toOver)
    (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) x y
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id] at hp
  have he := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_biextension M.abelian C.ampleLine (C.poincare.pullback (f ⊗ₘ 𝟙 M.abelian.toOver).left)
    (RepresentationTheory.Theta.Geometric.QuotientDifferenceFibers.quotientDifference_formulaIso p.isogeny C.ampleLine C.poincare C.difference)
  exact hp.symm.trans (LinearMap.congr_fun (LinearMap.congr_fun he x) y)

theorem PicardConstruction.ReferencePicardConstruction.periodPairing_left_ext (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian)
    (h : ∀ w, C.periodPairing x w = C.periodPairing y w) : x = y := by
  obtain ⟨u, rfl⟩ := (PicardConstruction.ReferencePicardConstruction.latticeIsogeny_period_bijective (p := p)).surjective x
  obtain ⟨v, rfl⟩ := (PicardConstruction.ReferencePicardConstruction.latticeIsogeny_period_bijective (p := p)).surjective y
  apply congrArg (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom))
  apply C.chernForm_left_ext
  intro w
  exact (C.periodPairing_isogeny u w).symm.trans ((h w).trans (C.periodPairing_isogeny v w))

theorem PicardConstruction.ReferencePicardConstruction.periodPairing_detects_group_maps (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f g : A.toOver ⟶ D.abelian.toOver) [IsMonHom f] [IsMonHom g]
    (h : ∀ x y, C.periodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) y = C.periodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g x) y) : f = g := by
  apply Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful f g
  apply LinearMap.ext
  intro x
  exact C.periodPairing_left_ext _ _ (h x)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
