import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualBaseChangeComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Polarization Point Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationPointBaseChange

noncomputable section

/-! The native dual-torsion image of an original point under the
polarization retains its full dual point through arbitrary field base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

attribute [local instance] DualityIntrinsicPointValues.Construction.e56PointPolarization_preserves BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (n : ℕ)

def originalNativePolarizationImage (T : Over (Spec (.of k)))
    (y : (A.abelian.torsionFunctor n).obj (.op T)) :
    T ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
  (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y ≫
    CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).map n) ≫
      TorsionQuotient.SubgroupFunctor.torsionι (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).dual.abelian n

theorem originalNativePolarizationPoint_inclusion (T : Over (Spec (.of k)))
    (y : (A.abelian.torsionFunctor n).obj (.op T)) :
    (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y ≫
        CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).map n) ≫
      TorsionQuotient.SubgroupFunctor.torsionι (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).dual.abelian n =
        y.val ≫ (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).map := by
  let p := HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization
  let z := IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A.abelian n T y
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => z ≫ h) (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion p.map n)).trans
      ((Category.assoc z (TorsionQuotient.SubgroupFunctor.torsionι A.abelian.scheme n) p.map).symm.trans
        (congrArg (fun h => h ≫ p.map) (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint_inclusion A.abelian n T y))))

variable {k' : Type} [Field k'] [IsAlgClosed k'] (s : Spec (.of k') ⟶ Spec (.of k))

theorem originalNativePolarizationPoint_baseChange (Q : Over (Spec (.of k')))
    (y : ((A.pullback s).abelian.torsionFunctor n).obj (.op Q)) :
    Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian s Q
      (originalNativePolarizationImage (A.pullback s) n Q y) =
      originalNativePolarizationImage A n ((Over.map s).obj Q)
        (A.abelian.torsionBaseChangeEquiv s Q n y) := by
  have hp := originalNativePolarizationPoint_inclusion (A.pullback s) n Q y
  have ho := originalNativePolarizationPoint_inclusion A n ((Over.map s).obj Q)
    (A.abelian.torsionBaseChangeEquiv s Q n y)
  have h := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm y.val
    (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization).map
  exact (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian s Q) hp).trans
    (h.trans ho.symm)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationPointBaseChange
