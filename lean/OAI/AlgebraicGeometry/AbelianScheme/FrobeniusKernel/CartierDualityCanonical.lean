import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter

/-! # Cartier Duality Canonical -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction

noncomputable section

/-! Apply the complete canonical CartierDuality theorem at 685bb25 to the original
polarized source. Its finite-flat polarization degree comes from the
given HilbertConstruction polarization type, including nonreduced kernel length. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (n : ℕ) (hn : 0 < n)

def e56SourceTorsionPairing :
    CartierDuality.PolarizedTorsion.BilinearPairing (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n)
      (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) :=
  CartierDuality.PolarizedTorsion.Polarization.torsionPairing (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization) n hn

theorem e56SourcePolarization_fiberDegree (s : Spec (.of k)) :
    CartierDuality.PolarizedTorsion.Polarization.fiberDegree (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization) s = (∏ i, δ i) ^ 2 :=
  A.polarization.kernelType.degree _

include hn in
theorem e56SourceTorsion_finiteLocallyFree :
    CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n) :=
  CartierDuality.PolarizedTorsion.Polarization.torsion_finiteLocallyFree (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization) n hn

theorem e56SourceTorsionPairing_isPerfect (hdegree : n.Coprime (∏ i, δ i)) :
    CartierDuality.PolarizedTorsion.IsPerfectPairing (e56SourceTorsionPairing A n hn) := by
  apply CartierDuality.PolarizedTorsion.Polarization.torsionPairing_isPerfect (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization) n hn
  intro s
  rw [e56SourcePolarization_fiberDegree]
  exact hdegree.pow_right 2

theorem e56SourcePrimePowerPairing_isPerfect {q : ℕ} [Fact q.Prime]
    (hdegree : q.Coprime (∏ i, δ i)) (r : ℕ) :
    CartierDuality.PolarizedTorsion.IsPerfectPairing (e56SourceTorsionPairing A (q ^ r)
      (pow_pos (Fact.out : q.Prime).pos r)) :=
  e56SourceTorsionPairing_isPerfect A (q ^ r) (pow_pos (Fact.out : q.Prime).pos r) (hdegree.pow_left r)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction
