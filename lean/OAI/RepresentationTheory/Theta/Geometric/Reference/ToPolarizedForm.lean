import OAI.RepresentationTheory.Theta.Geometric.Reference.PoincareDetection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps

/-! # To Polarized Form -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.ToPolarizedForm

noncomputable section

/-! An original reference-to-polarized isomorphism preserves the exact
rational polarization form, through its Poincare and isogeny equations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps.AbelianIntrinsicAdapter

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} (C : PolarizationConstruction.ReferencePolarizationConstruction p)
    {level : ℕ} (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType level AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : M.abelian.toOver ≅ B.abelian.scheme) (d : N.abelian.toOver ≅ B.dual.abelian.scheme)
    [IsMonHom e.hom] [IsMonHom d.hom]
    (hpol : p.isogeny.hom ≫ d.hom = e.hom ≫ B.polarization.isogeny.hom)
    (hpoincare : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ e.hom).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)

include hpol hpoincare in
 theorem referenceToPolarized_period_form (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    let CB := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B)
    let f : M.abelian.toOver ⟶ CB.toOver := e.hom
    let : IsMonHom f := inferInstanceAs (IsMonHom e.hom)
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm B (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  let CB := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B)
  let DB := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.dual.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Projectivity.dualNativeProjectivePresentation B)
  let f : M.abelian.toOver ⟶ CB.toOver := e.hom
  let t : N.abelian.toOver ⟶ DB.toOver := d.hom
  let : IsMonHom f := inferInstanceAs (IsMonHom e.hom)
  let : IsMonHom t := inferInstanceAs (IsMonHom d.hom)
  have he : (show M.abelian.toOver ⟶ N.abelian.toOver from p.isogeny.hom) ≫ t =
      f ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodIso.nativePolarizationMap B := by
    apply Over.OverMorphism.ext
    have hh := congrArg Over.Hom.left hpol
    simpa only [Over.comp_left, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodIso.nativePolarizationMap_left] using hh
  have heq := LinearMap.congr_fun (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ he) x
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp] at heq
  have hpair := LinePeriodPairing.linePeriodPairing_pullback N.abelian M.abelian DB CB t f
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) y
  rw [hpoincare] at hpair
  change C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) y =
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing.nativePoincarePeriodPairing B (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift t (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x))
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) at hpair
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift t (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) =
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodIso.nativePolarizationPeriodIso B (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) at heq
  rw [heq, AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing.nativePoincarePeriodPairing_polarization] at hpair
  exact hpair.symm.trans (C.periodPairing_isogeny x y)

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.ToPolarizedForm
