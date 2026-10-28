import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPositiveDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GroundFormulaGeometricPositivity

/-! # Weil Polarization Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizationDescent

noncomputable section

/-! Canonical Weil maximal isotropy constructs the actual unique quotient polarization of unchanged type over an algebraically closed field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Kernel.Scheme.kernelGroup
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

/-- A polarization record is determined by its actual isogeny. -/
theorem polarization_ext {S : Scheme} {a : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A}
    {δ : Fin a → ℕ} (p q : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (h : p.isogeny = q.isogeny) : p = q := by
  cases p
  cases q
  cases h
  rfl

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- The quotient polarization includes geometric positivity, finite flat isogeny geometry, and the unchanged full kernel type. -/
theorem existsUnique_polarization (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : WeilData.SelfAnnihilating DA pol.isogeny n hn
      (Kernel.ContainmentMap.torsionMap f.hom n hf)) :
    ∃! m : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      f.hom ≫ m.isogeny.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ n := by
  obtain ⟨m, hm, hu⟩ := WeilPositiveDescent.existsUnique_positive_isogeny DA DB pol f n hn hnd hf hlag
  let p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ := {
    isogeny := m
    kernelType := hm.2.1
    positive := fun K _ _ s => GroundFormulaGeometricPositivity.positiveOnGeometricFiber DB m.hom hm.2.2 K s }
  refine ⟨p, hm.1, ?_⟩
  intro r hr
  apply polarization_ext r p
  exact hu r.isogeny ⟨hr, r.kernelType, Reference.PositiveFormula.of_polarization DB r⟩

/-- Prime-power polarization descent retains characteristic-q and infinitesimal test schemes. -/
theorem existsUnique_primePower_polarization (q h : ℕ) (hq : q.Prime) (hqd : q.Coprime (∏ i, δ i))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ h) = 1)
    (hlag : WeilData.SelfAnnihilating DA pol.isogeny (q ^ h) (pow_pos hq.pos h)
      (Kernel.ContainmentMap.torsionMap f.hom (q ^ h) hf)) :
    ∃! m : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      f.hom ≫ m.isogeny.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ (q ^ h) :=
  existsUnique_polarization DA DB pol f (q ^ h) (pow_pos hq.pos h) ((hqd.pow_right 2).pow_left h) hf hlag

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizationDescent
