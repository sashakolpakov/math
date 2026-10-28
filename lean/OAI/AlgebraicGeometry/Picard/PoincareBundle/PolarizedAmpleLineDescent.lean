import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicAmpleDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

/-! # Polarized Ample Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizedAmpleLineDescent

noncomputable section

/-! The given polarization supplies the entire positive source formula for ample inducing-line descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom n hf)
    (PolarizationTorsionPairing.pairing D pol n))

include hn hlag

/-- Full torsion self-annihilation constructs an ample quotient line whose pullback induces the prescribed multiple. -/
theorem exists_ample_inducing_pullback :
    ∃ N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left,
      N.IsAmple ∧ Nonempty ((N.pullback η[B.scheme].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (pol.isogeny.hom ^ n)).sheaf
          ((N.pullback f.hom.left).pullback (fst A.scheme A.scheme).left).sheaf)
        ((N.pullback f.hom.left).pullback (snd A.scheme A.scheme).left).sheaf ≅
          ((N.pullback f.hom.left).pullback μ[A.scheme].left).sheaf) :=
  Reference.IsotropicAmpleDescent.exists_ample_inducing_pullback D pol.isogeny.hom
    (PolarizationTorsionPairing.inducingLine D pol) (PolarizationTorsionPairing.inducingLine_formula D pol) n hn f hf hlag
    (Reference.PositiveFormula.of_polarization D pol)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizedAmpleLineDescent
