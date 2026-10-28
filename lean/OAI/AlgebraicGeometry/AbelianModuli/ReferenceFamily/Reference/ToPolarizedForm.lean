import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardPolarizationComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps

/-! # To Polarized Form -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ToPolarizedForm

noncomputable section

/-! An original reference-to-polarized isomorphism preserves the exact
rational polarization form, through its Poincare and isogeny equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps.AbelianIntrinsicAdapter

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {N : DualModel.ReferenceDualModel F hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M N} (C : PicardConstruction.ReferencePicardConstruction p)
    {level : ℕ} (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType level Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : M.abelian.toOver ≅ B.abelian.scheme) (d : N.abelian.toOver ≅ B.dual.abelian.scheme)
    [heGroup : IsMonHom e.hom] [hdGroup : IsMonHom d.hom]
    (hpol : p.isogeny.hom ≫ d.hom = e.hom ≫ B.polarization.isogeny.hom)
    (hpoincare : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ e.hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare)

include hpol hpoincare in
theorem referenceToPolarized_period_form (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    let CB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)
    let f : M.abelian.toOver ⟶ CB.toOver := e.hom
    let : IsMonHom f := inferInstanceAs (IsMonHom e.hom)
    Intrinsic.ChernPairing.nativePolarizationForm B (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
      Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  let CB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)
  let DB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation B)
  let f : M.abelian.toOver ⟶ CB.toOver := e.hom
  let t : N.abelian.toOver ⟶ DB.toOver := d.hom
  have : IsMonHom f := inferInstanceAs (IsMonHom e.hom)
  have : IsMonHom t := inferInstanceAs (IsMonHom d.hom)
  have : IsMonHom (show M.abelian.toOver ⟶ N.abelian.toOver from p.isogeny.hom) :=
    p.isogeny.preservesGroup
  have he : (show M.abelian.toOver ⟶ N.abelian.toOver from p.isogeny.hom) ≫ t =
      f ≫ Polarization.PeriodIso.nativePolarizationMap B := by
    apply Over.OverMorphism.ext
    exact (congrArg Over.Hom.left hpol).trans
      (congrArg (fun a => e.hom.left ≫ a) (Polarization.PeriodIso.nativePolarizationMap_left B)).symm
  have heq := LinearMap.congr_fun (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ he) x
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp] at heq
  have hraw := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback N.abelian M.abelian DB CB t f
    (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) y
  have hp : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t ⊗ₘ f).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare := hpoincare
  have hpair := (congrArg (fun L => RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing N.abelian M.abelian L
    (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) y) hp).symm.trans hraw
  change C.referencePeriodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) y =
    PoincarePeriodPairing.nativePoincarePeriodPairing B (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift t (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x))
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) at hpair
  change Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift t (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) =
    Polarization.PeriodIso.nativePolarizationPeriodIso B (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) at heq
  rw [heq, PoincarePeriodPairing.nativePoincarePeriodPairing_polarization] at hpair
  exact hpair.symm.trans (C.referencePeriodPairing_isogeny x y)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ToPolarizedForm
