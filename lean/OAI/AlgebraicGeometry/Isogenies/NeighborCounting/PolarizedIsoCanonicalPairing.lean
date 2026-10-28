import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingMorphism
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.UnbundledPicardComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

/-! # Polarized Iso Canonical Pairing -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedIsoCanonicalPairing

noncomputable section

/-! A genuine polarized source isomorphism preserves the canonical
scheme pairing. Its dual map is derived from the original Poincare equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingMorphism
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

theorem originalPicardPullbackGroup_hom {S : Scheme} {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    (AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.scheme B.scheme f
      (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA).withPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB).withPicardGroup).hom.hom =
      AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB := by
  rw [AbelianScheme.FrobeniusKernel.UnbundledPicardComparison.Construction.IntrinsicPicardPullback.dualMap_eq_unbundled]
  rfl

variable {S : Scheme} {g N : ℕ} {δ : Fin g → ℕ}
  {A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S} (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)

theorem polarizedIso_inverse_dual_poincare :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dual.inv ⊗ₘ 𝟙 A.abelian.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 B.dual.abelian.scheme ⊗ₘ e.abelian.hom).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) := by
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dual.inv ⊗ₘ 𝟙 A.abelian.scheme).left) e.poincare.symm
  have hm : (e.dual.inv ⊗ₘ 𝟙 A.abelian.scheme) ≫ (e.dual.hom ⊗ₘ e.abelian.hom) =
      𝟙 B.dual.abelian.scheme ⊗ₘ e.abelian.hom := by
    rw [tensorHom_comp_tensorHom, Iso.inv_hom_id, Category.id_comp]
  exact h.trans ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp _ _ _).symm.trans
    (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare))
      (congrArg (fun f => f.left) hm)))

theorem polarizedIso_canonical_dual :
    AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.abelian.hom A.dual B.dual = e.dual.inv :=
  (AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare e.abelian.hom A.dual B.dual e.dual.inv
    (polarizedIso_inverse_dual_poincare e)).symm

theorem polarizedIso_canonical_polarization :
    e.abelian.hom ≫ B.polarization.isogeny.hom ≫
      AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.abelian.hom A.dual B.dual = A.polarization.isogeny.hom := by
  rw [polarizedIso_canonical_dual, ← Category.assoc, ← e.polarization,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [IsReduced S] [IsLocallyNoetherian S]

theorem polarizedIso_canonical_pairing (n : ℕ) (hn : 0 < n) (T : Over S)
    (x y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme n) :
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing B.abelian B.dual B.polarization n hn).pairValue
        (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n e.abelian.hom) (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n e.abelian.hom) =
      (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization n hn).pairValue x y := by
  let A₀ : CartierDuality.PolarizedTorsion.AbelianScheme S := AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A.abelian
  let B₀ : CartierDuality.PolarizedTorsion.AbelianScheme S := AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction B.abelian
  let p₀ : CartierDuality.PolarizedTorsion.Polarization A₀ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction A.abelian A.dual A.polarization
  let p₁ : CartierDuality.PolarizedTorsion.Polarization B₀ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction B.abelian B.dual B.polarization
  let f : A₀.toOver ⟶ B₀.toOver := e.abelian.hom
  have : IsMonHom f := e.abelianGroup
  have hd := originalPicardPullbackGroup_hom A.abelian B.abelian A.dual B.dual e.abelian.hom
  have hp : f ≫ p₁.map ≫
      (AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A₀.toOver B₀.toOver f p₀.dual p₁.dual).hom.hom = p₀.map :=
    (congrArg (fun f => e.abelian.hom ≫ B.polarization.isogeny.hom ≫ f) hd).trans
      (polarizedIso_canonical_polarization e)
  exact Canonical.PairingMorphism.canonicalPolarizationPairing_morphism A₀ B₀ p₀ p₁ n hn f hp T x y

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedIsoCanonicalPairing
