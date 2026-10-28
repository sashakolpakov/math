import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPoincareBundleValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PairingCanonicalValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingUniversalValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange

/-! # Canonical Poincare Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPoincarePairing.Construction

noncomputable section

/-! The canonical CartierDuality pairing equals the actual PoincareBundle Poincare pairing
as a scheme bicharacter, using the original normalized symmetries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf ≅
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf)
  (σn : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n)).sheaf ≅
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n)).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hdn : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σn =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n)) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n))
      (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)) σn =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
  (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (pol.isogeny.hom ^ n))
      (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)) σn =
    Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (pol.isogeny.hom ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D))

def fieldPoincarePairingOfSymmetry :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  Poincare.LineDescent.Construction.poincareNativeTorsionPairing pol.isogeny.hom (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) n σn hv
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange D) hh

include hd hdn in
theorem fieldCanonicalPairing_poincare_value_affine {Q : Over (Spec (.of k))} [IsAffine Q.left]
    (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x y =
      (fieldPoincarePairingOfSymmetry D pol n σn hv hh).pairValue x y := by
  apply CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective Q
  exact (CanonicalPoincareBundleValue.Construction.fieldCanonicalPairing_e45_value_affine D pol n hn σ σn hd hdn hv x y).trans
    (Poincare.PairingCanonicalValue.Construction.poincareNativeTorsionPairing_canonical_value pol.isogeny.hom (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) n σn hv
      (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange D) hh Q x y).symm

include hd hdn in
theorem fieldCanonicalPairing_eq_poincare :
    PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn = fieldPoincarePairingOfSymmetry D pol n σn hv hh := by
  have hK := Canonical.RelativePairing.Construction.canonicalNativeTorsion_finiteLocallyFree (PolarizationAdapter.Construction.fieldPolarizationOfHilbertConstruction A D pol) n hn
  have : IsFinite (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).hom := hK.1
  have : IsAffine (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).left :=
    isAffine_of_isAffineHom (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).hom
  have : IsAffineHom (fst (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)).left := by
    change IsAffineHom (CategoryTheory.Limits.pullback.fst
      (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).hom (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).hom)
    infer_instance
  have : IsAffine (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n ⊗ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).left :=
    isAffine_of_isAffineHom (fst (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)).left
  apply PairingUniversalValue.Construction.schemeBicharacter_eq_of_universal_value
  exact fieldCanonicalPairing_poincare_value_affine D pol n hn σ σn hd hdn hv hh _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPoincarePairing.Construction
