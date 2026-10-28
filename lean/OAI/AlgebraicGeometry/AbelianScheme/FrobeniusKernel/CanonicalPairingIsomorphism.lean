import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionActions
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.UnbundledPicardComparison

/-! # Canonical Pairing Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingIsomorphism

noncomputable section

/-! Full original polarized source isomorphisms preserve the canonical
orthogonality predicate in the independent kernel prescription. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

variable {k : Type} [Field k] {g : ℕ}

theorem originalTorsionSheafPoint_morphism
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (n : ℕ) (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (T : Over (Spec (.of k))) (x : (A.torsionFunctor n).obj (.op T)) :
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.scheme B.scheme f)) n).hom.app (.op T)
        (Prescription.Construction.originalTorsionSheafPoint A n T x) =
      Prescription.Construction.originalTorsionSheafPoint B n T ((PELModuli.CMPoints.DualityPairing.homOnTorsion A B f n).app (.op T) x) := by
  apply PrescriptionActions.Construction.originalTorsionSheafInclusion_injective B n T
  let a := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.scheme B.scheme f)
  have h := congrArg (fun t => t.hom.app (.op T) (Prescription.Construction.originalTorsionSheafPoint A n T x))
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap_inclusion a n)
  exact h.trans
    ((congrArg (fun z => a.hom.app (.op T) z) (PrescriptionActions.Construction.originalTorsionSheafPoint_inclusion A n T x)).trans
      (PrescriptionActions.Construction.originalTorsionSheafPoint_inclusion B n T
        ((PELModuli.CMPoints.DualityPairing.homOnTorsion A B f n).app (.op T) x)).symm)

variable {N : ℕ} {δ : Fin g → ℕ}
variable (A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem sourceNativeDualMap_morphism_eq (f : A.abelian.scheme ⟶ B.abelian.scheme) [IsMonHom f] :
    (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.abelian.scheme B.abelian.scheme f
      (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled B.dual).withPicardGroup).hom.hom =
        PicardPullback.Construction.IntrinsicPicardPullback.dualMap f A.dual B.dual :=
  (UnbundledPicardComparison.Construction.IntrinsicPicardPullback.dualMap_eq_unbundled f A.dual B.dual).symm

variable [IsAlgClosed k]

theorem canonicalTorsionOrthogonal_levelIso (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)
    (n : ℕ) (hn : 0 < n) (T : Over (Spec (.of k)))
    (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    Prescription.Construction.canonicalTorsionOrthogonal B n hn T
      ((PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian B.abelian e.abelian.hom n).app (.op T) x)
      ((PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian B.abelian e.abelian.hom n).app (.op T) y) ↔
    Prescription.Construction.canonicalTorsionOrthogonal A n hn T x y := by
  have : IsMonHom (show (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian).toOver ⟶
      (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled B.abelian).toOver from e.abelian.hom) := e.abelianGroup
  have hp := SourceTransport.Construction.levelIso_polarization_pullback e
  have hd := sourceNativeDualMap_morphism_eq A B e.abelian.hom
  have hpol : e.abelian.hom ≫ B.polarization.isogeny.hom ≫
      (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.abelian.scheme B.abelian.scheme e.abelian.hom
        (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).withPicardGroup
        (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled B.dual).withPicardGroup).hom.hom = A.polarization.isogeny.hom :=
    (congrArg (fun d => e.abelian.hom ≫ B.polarization.isogeny.hom ≫ d) hd).trans hp
  have hv := CartierDualityPolarizationNaturality.Construction.e56PolarizationPairing_morphism (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian)
    (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled B.abelian) (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled A.dual A.polarization)
    (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled B.dual B.polarization) n hn e.abelian.hom hpol T
    (Prescription.Construction.originalTorsionSheafPoint A.abelian n T x) (Prescription.Construction.originalTorsionSheafPoint A.abelian n T y)
  have hx := originalTorsionSheafPoint_morphism A.abelian B.abelian n e.abelian.hom T x
  have hy := originalTorsionSheafPoint_morphism A.abelian B.abelian n e.abelian.hom T y
  have hxy := congrArg₂
    (fun u v : (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled B.abelian) n).obj.obj (.op T) =>
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled B.abelian) n) T
        ((CartierDualityCanonical.Construction.e56SourceTorsionPairing B n hn).rightAdjoint.hom.app (.op T) v) u) hx hy
  exact iff_of_eq (congrArg (fun z => z = 1) (hxy.symm.trans hv))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingIsomorphism
