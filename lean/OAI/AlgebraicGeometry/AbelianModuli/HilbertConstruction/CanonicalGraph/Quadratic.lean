import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Ampleness

/-! # Quadratic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Symmetry, quadratic powers, and ample multiplication pullbacks of canonical polarized graph bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_symmetric :
    Nonempty ((A.graphBundle.pullback ι[A.abelian.scheme].left).sheaf ≅ A.graphBundle.sheaf) :=
  PoincareGraph.Quadratic.poincareGraphBundle_symmetric A.dual A.polarization.isogeny.hom

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_multiplication_iso (n : ℕ) :
    Nonempty ((A.graphBundle.pullback (A.abelian.multiplication n).left).sheaf ≅
      (A.graphBundle.tensorPower (n * n)).sheaf) :=
  PoincareGraph.PowerIsomorphism.poincareGraphBundle_multiplication_iso A.dual A.polarization.isogeny.hom n

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_multiplication_isTensorPower (n : ℕ) :
    Tensor.Powers.IsTensorPower A.graphBundle.sheaf (n * n)
      (A.graphBundle.pullback (A.abelian.multiplication n).left).sheaf :=
  PoincareGraph.PowerIsomorphism.poincareGraphBundle_multiplication_isTensorPower A.dual A.polarization.isogeny.hom n

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_multiplication_isAmple [IsAlgClosed K] (n : ℕ) (hn : 0 < n) :
    (A.graphBundle.pullback (A.abelian.multiplication n).left).IsAmple :=
  (A.graphBundle_isAmple_overAlgClosed.tensorPower (n * n) (Nat.mul_pos hn hn)).of_iso
    (A.graphBundle_multiplication_iso n).some.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
