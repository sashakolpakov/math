import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.StandardWeilPolarizedDescent

/-! # Weil Polarized Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizedDescent

noncomputable section

/-! Canonical standard Weil maximal isotropy and the original polarization determine the unique type-preserving quotient isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- The standard Weil hypothesis needs no auxiliary character representation, frame, line, or torsion-cover input. -/
theorem existsUnique_isogeny (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : WeilData.SelfAnnihilating DA pol.isogeny n hn
      (Kernel.ContainmentMap.torsionMap f.hom n hf)) :
    ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
      f.hom ≫ m.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = pol.isogeny.hom ^ n ∧
      m.HasPolarizationType δ :=
  StandardWeilPolarizedDescent.existsUnique_isogeny DA DB pol f n hn hnd
    (WeilData.representative DA pol.isogeny n hn) hf hlag

/-- Prime-power canonical Weil descent preserves type without assuming the prime is invertible in the field. -/
theorem existsUnique_primePower_isogeny (q h : ℕ) (hq : q.Prime) (hqd : q.Coprime (∏ i, δ i))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ h) = 1)
    (hlag : WeilData.SelfAnnihilating DA pol.isogeny (q ^ h) (pow_pos hq.pos h)
      (Kernel.ContainmentMap.torsionMap f.hom (q ^ h) hf)) :
    ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
      f.hom ≫ m.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ (q ^ h) ∧
      m.HasPolarizationType δ :=
  existsUnique_isogeny DA DB pol f (q ^ h) (pow_pos hq.pos h) ((hqd.pow_right 2).pow_left h) hf hlag

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizedDescent
