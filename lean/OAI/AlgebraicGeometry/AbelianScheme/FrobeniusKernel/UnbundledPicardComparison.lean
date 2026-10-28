import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarization
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData

/-! # Unbundled Picard Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.UnbundledPicardComparison.Construction.IntrinsicPicardPullback

noncomputable section

/-! The dimension-free and fixed-dimension native Picard constructions
use the same original pullback morphism and represented sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

theorem dualMap_eq_unbundled :
    PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB = Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback
      (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB) f := by
  rw [Polarization.Construction.NativePicardPullback.dualMap_eq_e57]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.UnbundledPicardComparison.Construction.IntrinsicPicardPullback
