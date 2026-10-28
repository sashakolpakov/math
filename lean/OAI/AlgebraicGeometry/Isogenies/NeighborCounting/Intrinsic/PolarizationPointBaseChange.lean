import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.TorsionPointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualBaseChangeComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues

/-! # Polarization Point Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.PolarizationPointBaseChange

noncomputable section

/-! The original polarization's native dual-torsion point retains its
full dual inclusion under arbitrary reduced-base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.TorsionPointBaseChange
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative
  AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative
  AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56PointPolarization_preserves

theorem nativePolarizationPoint_inclusion {S : Scheme} (A : CartierDuality.PolarizedTorsion.AbelianScheme S)
    (pol : CartierDuality.PolarizedTorsion.Polarization A) (n : ℕ) (Q : Over S)
    (y : Q ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) :
    ((y ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom) ≫
        AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap pol.map n) ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι pol.dual.abelian n =
      (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.toOver n) ≫ pol.map := by
  let z := y ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.toOver) n).inv.hom.hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => z ≫ a) (AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion pol.map n)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ pol.map) (TorsionPointBaseChange.nativeMultiplicationPoint_inclusion (Grp.mk A.toOver) n y))))

variable {S T : Scheme} [IsReduced S] [IsLocallyNoetherian S]
  [IsReduced T] [IsLocallyNoetherian T] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ}
  (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (s : T ⟶ S) (n : ℕ)

theorem reducedPolarizationPoint_baseChange (Q : Over T)
    (y : Q ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    let A₀ := AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A
    let p₀ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction A D pol
    let A₁ := AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)
    let p₁ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction (A.pullback s) (D.pullback s) (pol.pullback s)
    let y₀ := TorsionPointBaseChange.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n Q y
    Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian s Q
      (((y ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A₁.toOver) n).inv.hom.hom) ≫
        AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p₁.map n) ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι p₁.dual.abelian n) =
      ((y₀ ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A₀.toOver) n).inv.hom.hom) ≫
        AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p₀.map n) ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι p₀.dual.abelian n := by
  let A₀ := AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A
  let p₀ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction A D pol
  let A₁ := AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)
  let p₁ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction (A.pullback s) (D.pullback s) (pol.pullback s)
  let y₀ := TorsionPointBaseChange.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n Q y
  have h₁ := nativePolarizationPoint_inclusion A₁ p₁ n Q y
  have h₀ := nativePolarizationPoint_inclusion A₀ p₀ n ((Over.map s).obj Q) y₀
  have hp := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm
    (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A₁.toOver n) pol.isogeny.hom
  have hy := TorsionPointBaseChange.nativeTorsionOriginalPoint_inclusion s (Grp.mk A.scheme) n Q y
  exact (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).abelian s Q) h₁).trans
    (hp.trans ((congrArg (fun z => z ≫ p₀.map) hy.symm).trans h₀.symm))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.PolarizationPointBaseChange
