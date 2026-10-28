import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceKernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.KernelOriginCoordinates

/-! # Slice Torsion Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceTorsionCoordinates.Construction

noncomputable section

/-! The iterated-slice parameter and torsion coordinates recover the
same original points, through the actual kernel inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem parameterSliceTestIso_projection {S : Scheme.{u}} (Q : Over S) (V : Over Q) :
    (SliceKernelPoints.Construction.parameterSliceTestIso Q V).hom ≫ V.hom = CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q (SliceKernelPoints.Construction.parameterSliceTest Q V) := by
  apply Over.OverMorphism.ext
  exact Category.id_comp V.hom.left

set_option backward.isDefEq.respectTransparency false in
theorem parameterSliceTorsionCoordinate_original {k : Type} [Field k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (n : ℕ) (Q : Over (Spec (.of k))) (V : Over Q)
    (z : V.left ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate n (SliceKernelPoints.Construction.parameterSliceTest Q V)
      (SliceKernelPoints.Construction.parameterSliceKernelPoint Q ((𝟙 A.scheme) ^ n) V
        (z ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom)) =
      (SliceKernelPoints.Construction.parameterSliceTestIso Q V).hom ≫ z ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n := by
  have hi := congrArg (fun a => a.hom.hom) (MultiplicationKernelSheafComparison.Construction.multiplicationKernelNativeGroupIso_inv_inclusion (Grp.mk A.scheme) n)
  change (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom ≫
    Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n) = Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n at hi
  unfold Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate
  rw [SliceKernelPoints.Construction.parameterSliceKernelPoint_original, Category.assoc, Category.assoc, hi]

set_option backward.isDefEq.respectTransparency false in
theorem poincareDiagonalParameter_coordinates {k : Type} [Field k] {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (φ : A.scheme ⟶ D.abelian.scheme) (n : ℕ) {Q : Over (Spec (.of k))}
    (x : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    Poincare.KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D (x ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ φ)
      (SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q))) =
    Poincare.KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate n (SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q)))
      (SliceKernelPoints.Construction.parameterSliceKernelPoint Q ((𝟙 A.scheme) ^ n) (Over.mk (𝟙 Q))
        (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom)) ≫ φ := by
  rw [Poincare.KernelOriginCoordinates.Construction.poincareParameterDualCoordinate, parameterSliceTorsionCoordinate_original,
    ← parameterSliceTestIso_projection Q (Over.mk (𝟙 Q))]
  simp only [Category.assoc, Over.mk_hom]
  exact congrArg (fun a => (SliceKernelPoints.Construction.parameterSliceTestIso Q (Over.mk (𝟙 Q))).hom ≫ a)
    (Category.id_comp (x ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ φ))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SliceTorsionCoordinates.Construction
