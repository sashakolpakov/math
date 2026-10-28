import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange

/-! # Torsion Point Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.TorsionPointBaseChange

noncomputable section

/-! The native IsogenyQuotient torsion points and the character-line multiplication
kernel retain the same original point under arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange.Construction
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative
  AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

local instance torsionPointPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

variable {S T : Scheme} (s : T ⟶ S) (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)

def nativeTorsionOriginalPoint (Q : Over T)
    (x : Q ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme ((Over.pullback s).obj G.X) n) :
    (Over.map s).obj Q ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n :=
  (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) Q).symm
    (x ≫ (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s G n).inv)

theorem nativeTorsionOriginalPoint_inclusion (Q : Over T)
    (x : Q ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme ((Over.pullback s).obj G.X) n) :
    nativeTorsionOriginalPoint s G n Q x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion G.X n =
      Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv G.X s Q
        (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback s).obj G.X) n) := by
  have hi := congrArg (fun t => x ≫ t) (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso_inv_inclusion s G n)
  have hn := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm
    (x ≫ (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s G n).inv) (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion G.X n)
  exact hn.symm.trans (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv G.X s Q)
    ((Category.assoc _ _ _).trans hi))

theorem nativeMultiplicationPoint_inclusion {Q : Over S}
    (x : Q ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n) :
    (x ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv.hom.hom) ≫
      Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n) = x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion G.X n :=
  (Category.assoc _ _ _).trans
    (congrArg (fun a => x ≫ a)
      (congrArg (fun a => a.hom.hom) (AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison.Construction.multiplicationKernelNativeGroupIso_inv_inclusion G n)))

theorem nativeMultiplicationPoint_baseChange (Q : Over T)
    (x : Q ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme ((Over.pullback s).obj G.X) n) :
    AbelianScheme.FrobeniusKernel.CartierPicardBaseChange.Construction.nativeKernelBaseChangeAlongPoint s ((𝟙 G.X) ^ n)
        ((𝟙 ((Over.pullback s).obj G.X)) ^ n)
        (AbelianScheme.CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s G.X n).symm Q
        (x ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso ((Over.pullback s).mapGrp.obj G) n).inv.hom.hom) =
      nativeTorsionOriginalPoint s G n Q x ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv.hom.hom := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n)) := inferInstanceAs
    (Mono (CategoryTheory.Limits.equalizer.ι ((𝟙 G.X) ^ n) 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n))).mp
  have hp := AbelianScheme.FrobeniusKernel.CartierPicardBaseChange.Construction.nativeKernelBaseChangeAlongPoint_inclusion s ((𝟙 G.X) ^ n)
    ((𝟙 ((Over.pullback s).obj G.X)) ^ n)
    (AbelianScheme.CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s G.X n).symm Q
    (x ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso ((Over.pullback s).mapGrp.obj G) n).inv.hom.hom)
  have hx := congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv G.X s Q)
    (nativeMultiplicationPoint_inclusion ((Over.pullback s).mapGrp.obj G) n x)
  exact hp.trans (hx.trans ((nativeTorsionOriginalPoint_inclusion s G n Q x).symm.trans
    (nativeMultiplicationPoint_inclusion G n (nativeTorsionOriginalPoint s G n Q x)).symm))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.TorsionPointBaseChange
