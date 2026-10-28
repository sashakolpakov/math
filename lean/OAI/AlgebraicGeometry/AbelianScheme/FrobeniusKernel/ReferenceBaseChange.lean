import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationPointComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionBaseChange

/-! # Reference Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceBaseChange

noncomputable section

/-! Native source-kernel base change is the original HilbertConstruction torsion-point
base change, with the exact inclusion into the abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (s : S' ⟶ S) (n : ℕ)

theorem originalMultiplicationKernelPoint_baseChange (Q : Over S')
    (x : ((A.pullback s).torsionFunctor n).obj (.op Q)) :
    CartierPicardBaseChange.Construction.nativeKernelBaseChangeAlongPoint s ((𝟙 A.scheme) ^ n) ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n)
        (CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s A.scheme n).symm Q
        (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint (A.pullback s) n Q x) =
      IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint A n ((Over.map s).obj Q) (A.torsionBaseChangeEquiv s Q n x) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n)) := inferInstanceAs
    (Mono (CategoryTheory.Limits.equalizer.ι ((𝟙 A.scheme) ^ n) 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n))).mp
  have hp := CartierPicardBaseChange.Construction.nativeKernelBaseChangeAlongPoint_inclusion s ((𝟙 A.scheme) ^ n)
    ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n)
    (CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s A.scheme n).symm Q
    (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint (A.pullback s) n Q x)
  have hx := congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A.scheme s Q)
    (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint_inclusion (A.pullback s) n Q x)
  exact hp.trans (hx.trans
    (IntrinsicMultiplicationPointComparison.Construction.originalMultiplicationKernelPoint_inclusion A n ((Over.map s).obj Q)
      (A.torsionBaseChangeEquiv s Q n x)).symm)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceBaseChange
