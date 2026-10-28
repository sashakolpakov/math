import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPositiveDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GroundFormulaGeometricPositivity

/-! # Poincare Bundle Polarization Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PoincareBundlePolarizationDescent.Construction

noncomputable section

/-! Canonical full-kernel self-annihilation constructs the full original
polarization record, including positivity on every geometric fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag : Picard.PoincareBundle.Canonical.WeilData.SelfAnnihilating DA pol.isogeny n hn
    (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f.hom n hf))

def e45DescendedPolarization : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ where
  isogeny := Classical.choose
    (Picard.PoincareBundle.Canonical.WeilPositiveDescent.existsUnique_positive_isogeny DA DB pol f n hn hnd hf hlag)
  kernelType := (Classical.choose_spec
    (Picard.PoincareBundle.Canonical.WeilPositiveDescent.existsUnique_positive_isogeny DA DB pol f n hn hnd hf hlag)).1.2.1
  positive := Picard.PoincareBundle.GroundFormulaGeometricPositivity.positiveOnGeometricFiber DB _
    (Classical.choose_spec
      (Picard.PoincareBundle.Canonical.WeilPositiveDescent.existsUnique_positive_isogeny DA DB pol f n hn hnd hf hlag)).1.2.2

abbrev e45DescendedPolarization_pullback :=
  (Classical.choose_spec
    (Picard.PoincareBundle.Canonical.WeilPositiveDescent.existsUnique_positive_isogeny DA DB pol f n hn hnd hf hlag)).1.1

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PoincareBundlePolarizationDescent.Construction
