import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.StandardWeilValue
import OAI.AlgebraicGeometry.Picard.PoincareBundle.StandardWeilTypedDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

/-! # Standard Weil Polarized Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.StandardWeilPolarizedDescent

noncomputable section

/-! The original polarization and standard Weil maximal isotropy construct the unique type-preserving quotient isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation
open OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

/-- The given polarization supplies every auxiliary line and torsion-geometric input to the standard Weil descent theorem. -/
theorem existsUnique_isogeny (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
    (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
      (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
    (hlag : Reference.StandardWeilValue.SelfAnnihilating DA pol.isogeny n hn C
      (Kernel.ContainmentMap.torsionMap f.hom n hf)) :
    ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
      f.hom ≫ m.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = pol.isogeny.hom ^ n ∧
      m.HasPolarizationType δ := by
  have h := Reference.Torsion.cover DA pol.isogeny n hn
  have : IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.1
  have : Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.1
  have : Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.2.2.1
  have : IsAffine (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).left := h.2.2.2.2
  exact StandardWeilTypedDescent.existsUnique_isogeny DA DB pol.isogeny f δ pol.kernelType
    (PolarizationTorsionPairing.inducingLine DA pol) (PolarizationTorsionPairing.inducingLine_formula DA pol) n hn hnd C hf hlag

/-- Prime-power descent under standard Weil maximal isotropy preserves type in every characteristic. -/
theorem existsUnique_primePower_isogeny (q h : ℕ) (hq : q.Prime) (hqd : q.Coprime (∏ i, δ i))
    (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
      (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ (q ^ h)))))
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ h) = 1)
    (hlag : Reference.StandardWeilValue.SelfAnnihilating DA pol.isogeny (q ^ h) (pow_pos hq.pos h) C
      (Kernel.ContainmentMap.torsionMap f.hom (q ^ h) hf)) :
    ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
      f.hom ≫ m.hom ≫ DualMaps.representedDualMap
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom =
          pol.isogeny.hom ^ (q ^ h) ∧
      m.HasPolarizationType δ :=
  existsUnique_isogeny DA DB pol f (q ^ h) (pow_pos hq.pos h) ((hqd.pow_right 2).pow_left h) C hf hlag

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.StandardWeilPolarizedDescent
