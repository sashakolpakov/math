import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilCharacter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEvaluation

/-! # Poincare Weil Scalar -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilScalar.Construction

noncomputable section

/-! The canonical polarization pairing is the actual scalar cocycle
of the original torsion Poincare family and its constructed frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ)
  {Q : Over (Spec (.of k))}

def fieldPoincareTorsionScalar (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) : Γ(Q.left, ⊤) :=
  (Poincare.ParameterKernelCharacter.Construction.poincareParameterKernelCocycle D n
    (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom)
    (PoincareWeilCharacter.Construction.originalPolarization_torsionPoint_pow D pol n y)).value
      (1 : SliceKernelPoints.Construction.parameterSliceTest Q (Over.mk (𝟙 Q)) ⟶ (Over.pullback Q.hom).obj A.scheme)
      (SliceKernelPoints.Construction.parameterSliceKernelPoint Q ((𝟙 A.scheme) ^ n) (Over.mk (𝟙 Q))
        (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom))

variable (hn : 0 < n) [IsAffine Q.left]

theorem fieldPolarizationPairingCharacter_unit_value (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q (CartierDuality.Evaluation.Construction.CharacterEvaluation.value (PoincareWeilCharacter.Construction.fieldPolarizationPairingCharacter D pol n hn y)
      (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom)) : Γ(Q.left, ⊤)) =
        fieldPoincareTorsionScalar D pol n x y := by
  have hc := Reference.PositiveMultiplication.Construction.originalPositiveMultiplication_properties D pol n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hc.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hc.2.2.2
  let t := y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n ≫ pol.isogeny.hom
  let ht : t ^ n = 1 := PoincareWeilCharacter.Construction.originalPolarization_torsionPoint_pow D pol n y
  let z := x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A.scheme) n).inv.hom.hom
  have hv := Parameter.CharacterEvaluation.Construction.parameterCharacterSection_unit_value ((𝟙 A.scheme) ^ n) Q
    (Poincare.ParameterKernelCharacter.Construction.poincareParameterKernelCharacter D n t ht) (Poincare.ParameterKernelCharacter.Construction.poincareParameterKernelCharacter_natural D n t ht) z
  exact (congrArg Units.val hv).trans
    (Poincare.ParameterKernelCharacter.Construction.poincareParameterKernelCharacter_recovers D n t ht 1
      (SliceKernelPoints.Construction.parameterSliceKernelPoint Q ((𝟙 A.scheme) ^ n) (Over.mk (𝟙 Q)) z)).symm

theorem fieldNativePolarizationPairing_poincare_scalar (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q ((PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x y) : Γ(Q.left, ⊤)) =
      fieldPoincareTorsionScalar D pol n x y :=
  (congrArg (fun a => (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom Q a : Γ(Q.left, ⊤)))
    (PoincareWeilCharacter.Construction.fieldNativePolarizationPairing_poincare_character D pol n hn x y)).trans
      (fieldPolarizationPairingCharacter_unit_value D pol n hn x y)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PoincareWeilScalar.Construction
