import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.IntrinsicWeilValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionWeilBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilBaseChange

/-! # Weil Point Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.WeilPointBaseChange.Construction

noncomputable section

/-! The polarization image and its actual Weil character evaluation
retain the original native torsion points through base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilBaseChange.Construction
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {S S' : Scheme}
  {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (hD : GlobalFunctions.Construction.HasUniversalGlobalFunctions D.abelian.scheme)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (s : S' ⟶ S)

set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionWeilImage_baseChange (T : Over S')
    (y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    let p0 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction A D pol hD
    let p1 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction (A.pullback s) (D.pullback s) (pol.pullback s) (hD.pullback s)
    let y0 := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y
    let yp := (y ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso (A.pullback s).scheme n).inv) ≫
      CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p1.map n
    let yq := (y0 ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.scheme n).inv) ≫
      CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p0.map n
    Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv p0.representation.abelian s T
      (yp ≫ TorsionQuotient.SubgroupFunctor.torsionι p1.dual.abelian n) = yq ≫ TorsionQuotient.SubgroupFunctor.torsionι p0.dual.abelian n := by
  dsimp only
  let p0 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction A D pol hD
  let p1 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction (A.pullback s) (D.pullback s) (pol.pullback s) (hD.pullback s)
  let y0 := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y
  have hi1 := Relative.IntrinsicWeilValue.Construction.nativeTorsionWeilImage_inclusion p1 n T y
  have hi0 := Relative.IntrinsicWeilValue.Construction.nativeTorsionWeilImage_inclusion p0 n ((Over.map s).obj T) y0
  have h := AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map pol.isogeny.hom s T
    (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
  exact (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv p0.representation.abelian s T) hi1).trans
    (h.trans ((congrArg (fun z => z ≫ p0.map)
      (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint_inclusion s (Grp.mk A.scheme) n T y).symm).trans hi0.symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.WeilPointBaseChange.Construction
