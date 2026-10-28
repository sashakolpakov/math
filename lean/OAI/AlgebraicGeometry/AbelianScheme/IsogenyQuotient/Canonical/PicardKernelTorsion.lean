import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.PullbackKernelTorsion

/-! # Picard Kernel Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardKernelTorsion.Construction

noncomputable section

/-! The original canonical dual's actual Picard pullback kernel is
killed by the finite-flat degree, on all parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {X : Over S} [GrpObj X] (f : X ⟶ A.scheme) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]
  (d : ℕ) (hdegree : ∀ a : A.scheme.left, f.left.finrank a = d)

include hdegree in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalPicardPullback_kernel_pow (T : Over S)
    (z : T ⟶ (DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
    (hz : PicardPullback.Construction.canonicalPicardPullbackHom D f T z = 1) : z ^ d = 1 := by
  have h := Picard.PullbackKernelTorsion.Construction.homogeneousPicardPullback_kernel_pow f d hdegree T
    ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv z) hz
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)
  apply (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) T).injective
  rw [map_pow, map_one]
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardKernelTorsion.Construction
