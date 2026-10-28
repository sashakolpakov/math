import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Torsion Kernel Group Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionKernelGroupIso.CM

noncomputable section

/-! The multiplication kernel used by Cartier duality is the original
abelian torsion group scheme, through its unchanged full functor of points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (n : ℕ)

def kernelTorsionIso :
    Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) ≅ Grp.mk (A.torsionScheme n) :=
  yonedaGrpFullyFaithful.preimageIso
    (AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor.Construction.multiplicationKernelYonedaIso A n ≪≫ (A.torsionSchemeYonedaIso n).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionKernelGroupIso.CM
