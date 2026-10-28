import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionReferencePoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange

/-! # Torsion Weil Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionWeilBaseChange.Construction

noncomputable section

/-! The native torsion comparison preserves the original points in
the equalizer model used by Weil character evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange.Construction
attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

set_option backward.isDefEq.respectTransparency false in
theorem nativeTorsionOriginalPoint_equalizer
    {S S' : Scheme} (s : S' ⟶ S) (G : Grp (Over S)) [IsCommMonObj G.X]
    (n : ℕ) (T : Over S')
    (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme ((Over.pullback s).obj G.X) n) :
    FrobeniusKernel.CartierPicardBaseChange.Construction.nativeKernelBaseChangeAlongPoint s ((𝟙 G.X) ^ n)
      ((𝟙 ((Over.pullback s).obj G.X)) ^ n)
      (CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s G.X n).symm T
      (x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso ((Over.pullback s).obj G.X) n).inv) =
    TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s G n T x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso G.X n).inv := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n)) :=
    inferInstanceAs (Mono (equalizer.ι ((𝟙 G.X) ^ n) 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n))).mp
  rw [FrobeniusKernel.CartierPicardBaseChange.Construction.nativeKernelBaseChangeAlongPoint_inclusion]
  change Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv G.X s T
      ((x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso ((Over.pullback s).obj G.X) n).inv) ≫
        TorsionQuotient.SubgroupFunctor.torsionι ((Over.pullback s).obj G.X) n) =
    (TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s G n T x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso G.X n).inv) ≫
      TorsionQuotient.SubgroupFunctor.torsionι G.X n
  rw [Category.assoc, TorsionComparison.Construction.torsionEqualizerKernelIso_inv_inclusion,
    Category.assoc, TorsionComparison.Construction.torsionEqualizerKernelIso_inv_inclusion]
  exact (TorsionReferencePoint.Construction.nativeTorsionOriginalPoint_inclusion s G n T x).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionWeilBaseChange.Construction
