import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.WeilPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.TypedDescent

/-! # Standard Weil Typed Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.StandardWeilTypedDescent

noncomputable section

/-! Standard Weil self-annihilation constructs the unique type-preserving descended isogeny from the original data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Kernel.Scheme.kernelGroup

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.BundledDual

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A DA.abelian) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (δ : Fin g → ℕ) (ht : ell.HasPolarizationType δ)
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) ell.hom).sheaf
      (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf))
  (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
  [IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [IsAffine (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k))
    (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))))
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag : ∀ (T : Over (Spec (.of k))) (y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)),
    (∀ (U : Over (Spec (.of k))) (a : U ⟶ T) (x : U ⟶ Kernel.Scheme.kernelObject f.hom),
      Reference.WeilPairing.value DA ell n hn C (x ≫ Kernel.ContainmentMap.torsionMap f.hom n hf)
        (a ≫ y) = 1) ↔ ∃ x : T ⟶ Kernel.Scheme.kernelObject f.hom, x ≫ Kernel.ContainmentMap.torsionMap f.hom n hf = y)

include ht hformula hnd hlag

/-- Actual standard Weil maximal isotropy gives the unique descended isogeny and preserves its entire finite-kernel type. -/
theorem existsUnique_isogeny : ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
    f.hom ≫ m.hom ≫ DualMaps.representedDualMap
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = ell.hom ^ n ∧
    m.HasPolarizationType δ := by
  have hs := Reference.WeilPairing.selfAnnihilating DA ell n hn C L hformula
    (Kernel.ContainmentMap.torsionMap f.hom n hf) hlag
  obtain ⟨m, hm, hu⟩ := Reference.TypedDescent.existsUnique_isogeny (Canonical.BundledDual.canonical DA) DB (Canonical.BundledDual.isogeny DA ell) f δ
    ((Canonical.BundledDual.hasPolarizationType DA ell δ).mpr ht) L hformula n hn hnd hf hs
  have hp : (Canonical.BundledDual.isogeny DA ell).hom ^ n = ell.hom ^ n :=
    GivenDualGroupCompatibility.pow_eq (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA) ell.hom n
  refine ⟨m, ⟨hm.1.trans hp, hm.2⟩, ?_⟩
  intro r hr
  exact hu r ⟨hr.1.trans hp.symm, hr.2⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.StandardWeilTypedDescent
