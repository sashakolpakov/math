import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionSymmetryRatio
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleValueFormula

/-! # Torsion Value Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionValueComparison.Construction

noncomputable section

/-! The torsion scalar-frame ratio is exactly the canonical PoincareBundle
kernel value on the same original n-torsion points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ] (n : ℕ)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (σn : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hdn : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σn =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n))
      (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)) σn =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))

include hd hdn in
theorem poincareTorsionScalarFrame_e45Value {T : Over (Spec (.of k))}
    (z w : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (x y : T ⟶ A.scheme)
    (hz : z ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n = x) (hw : w ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n = y)
    (hx : x ^ n = 1) (hy : y ^ n = 1) (ht : (y ≫ φ) ^ n = 1) :
    Picard.PoincareBundle.Line.FrameUnits.frameRatio (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (y ≫ φ) (1 : T ⟶ A.scheme)) (lift_snd _ _))
      (ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n (y ≫ φ) x ht (lift (y ≫ φ) 1) (congrArg (lift (y ≫ φ)) hx)) =
    Picard.PoincareBundle.Canonical.KernelPairing.value (φ ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)
      ((𝟙 A.scheme) ^ n) (Picard.PoincareBundle.TorsionPairing.Poincare.torsion_annihilation φ n) σn hv z w :=
  (TorsionSymmetryRatio.Construction.poincareTorsionScalarFrame_symmetryRatio D φ n σ σn hd hdn x y hx hy ht).trans
    (BundleValueFormula.Construction.e45PoincareValue_frameRatio D (φ ^ n) σn ((𝟙 A.scheme) ^ n)
      (Picard.PoincareBundle.TorsionPairing.Poincare.torsion_annihilation φ n) hv z w x y hz hw
      (TorsionTransport.Construction.poincarePowerCoordinate_eq_one D φ n x hx) (TorsionTransport.Construction.poincarePowerCoordinate_eq_one D φ n y hy)).symm

include hd hdn in
theorem poincareTorsionScalarFrame_e45Value_of_coordinate {T : Over (Spec (.of k))}
    (z w : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (t : T ⟶ D.abelian.scheme) (x y : T ⟶ A.scheme)
    (hz : z ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n = x) (hw : w ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n = y)
    (hx : x ^ n = 1) (hy : y ^ n = 1) (ht : t ^ n = 1) (hta : t = y ≫ φ) :
    Picard.PoincareBundle.Line.FrameUnits.frameRatio (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t (1 : T ⟶ A.scheme)) (lift_snd _ _))
      (ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n t x ht (lift t 1) (congrArg (lift t) hx)) =
    Picard.PoincareBundle.Canonical.KernelPairing.value (φ ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)
      ((𝟙 A.scheme) ^ n) (Picard.PoincareBundle.TorsionPairing.Poincare.torsion_annihilation φ n) σn hv z w := by
  subst t
  exact poincareTorsionScalarFrame_e45Value D φ n σ σn hd hdn hv z w x y hz hw hx hy ht

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionValueComparison.Construction
