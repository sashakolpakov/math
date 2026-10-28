import OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.TypedDescent

/-! # Polarized Typed Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizedTypedDescent

noncomputable section

/-! Unique type-preserving isogeny descent uses only the original polarization, quotient isogeny and full torsion self-annihilation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- The original polarization gives the unique quotient isogeny and its unchanged finite-kernel type. -/
theorem existsUnique_isogeny (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom n hf) (PolarizationTorsionPairing.pairing DA pol n)) :
    ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
      f.hom ≫ m.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = pol.isogeny.hom ^ n ∧
      m.HasPolarizationType δ :=
  Reference.TypedDescent.existsUnique_isogeny DA DB pol.isogeny f δ pol.kernelType
    (PolarizationTorsionPairing.inducingLine DA pol) (PolarizationTorsionPairing.inducingLine_formula DA pol) n hn hnd hf hlag

/-- Prime-power descent retains the same type without assuming that the prime is invertible in the field. -/
theorem existsUnique_primePower_isogeny (q h : ℕ) (hq : q.Prime) (hqd : q.Coprime (∏ i, δ i))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ h) = 1)
    (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom (q ^ h) hf)
      (PolarizationTorsionPairing.pairing DA pol (q ^ h))) :
    ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
      f.hom ≫ m.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = pol.isogeny.hom ^ (q ^ h) ∧
      m.HasPolarizationType δ :=
  existsUnique_isogeny DA DB pol f (q ^ h) (pow_pos hq.pos h) ((hqd.pow_right 2).pow_left h) hf hlag

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizedTypedDescent
