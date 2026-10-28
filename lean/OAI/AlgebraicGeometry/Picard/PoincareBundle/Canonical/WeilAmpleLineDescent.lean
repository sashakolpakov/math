import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicAmpleDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

/-! # Weil Ample Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilAmpleLineDescent

noncomputable section

/-! Standard Weil self-annihilation constructs an actual ample quotient line, retaining the inducing formula after pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.BundledDual

attribute [local instance] Kernel.Scheme.kernelGroup
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag : WeilData.SelfAnnihilating D pol.isogeny n hn
    (Kernel.ContainmentMap.torsionMap f.hom n hf))

include hlag

/-- The standard pairing hypothesis needs no auxiliary line, frame, character representative, or torsion-cover hypothesis. -/
theorem exists_ample_inducing_pullback :
    ∃ N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left,
      N.IsAmple ∧ Nonempty ((N.pullback η[B.scheme].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (pol.isogeny.hom ^ n)).sheaf
          ((N.pullback f.hom.left).pullback (fst A.scheme A.scheme).left).sheaf)
        ((N.pullback f.hom.left).pullback (snd A.scheme A.scheme).left).sheaf ≅
          ((N.pullback f.hom.left).pullback μ[A.scheme].left).sheaf) := by
  have h := Reference.Torsion.cover D pol.isogeny n hn
  have : IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.1
  have : Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.1
  have : Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left := h.2.2.2.1
  have : IsAffine (Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)).left := h.2.2.2.2
  have hs := Reference.WeilPairing.selfAnnihilating D pol.isogeny n hn
    (WeilData.representative D pol.isogeny n hn)
    (PolarizationTorsionPairing.inducingLine D pol) (PolarizationTorsionPairing.inducingLine_formula D pol) (Kernel.ContainmentMap.torsionMap f.hom n hf) hlag
  obtain ⟨N, hN, o, ⟨formula⟩⟩ := Reference.IsotropicAmpleDescent.exists_ample_inducing_pullback
    (BundledDual.canonical D) (BundledDual.isogeny D pol.isogeny).hom (PolarizationTorsionPairing.inducingLine D pol) (PolarizationTorsionPairing.inducingLine_formula D pol)
    n hn f hf hs (Reference.PositiveFormula.of_polarization D pol)
  have hp : (BundledDual.isogeny D pol.isogeny).hom ^ n = pol.isogeny.hom ^ n :=
    GivenDualGroupCompatibility.pow_eq (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) pol.isogeny.hom n
  let e : (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared (BundledDual.canonical D).poincare) ((BundledDual.isogeny D pol.isogeny).hom ^ n)).sheaf ≅
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (pol.isogeny.hom ^ n)).sheaf :=
    (Scheme.Modules.pullbackCongr (congrArg (fun p : A.scheme ⟶ D.abelian.scheme =>
      (p ⊗ₘ 𝟙 A.scheme).left) hp)).app D.poincare.sheaf
  exact ⟨N, hN, o, ⟨AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e.symm (Iso.refl _)) (Iso.refl _) ≪≫ formula⟩⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilAmpleLineDescent
