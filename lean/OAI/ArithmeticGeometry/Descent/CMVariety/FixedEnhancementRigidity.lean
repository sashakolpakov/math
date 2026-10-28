import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicEnhancement
import OAI.ArithmeticGeometry.Descent.CMVariety.EquivariantRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.Canonical

/-! # Fixed Enhancement Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FixedEnhancementRigidity.Abelian.IntrinsicPeriods

noncomputable section

/-! The same constructed CM tuple controls every marked transverse period chart. -/

open _root_.CategoryTheory

variable {Index : Type} [Fintype Index]

theorem fixed_enhancement_marked_group_iso
    {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (E : AlgebraicEnhancement.Abelian.CMEnhancement A) (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A)
    (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (HB : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (B.variety.rationalCohomology 1))
    (hHB : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 B.variety HB)
    (k : Fin E.size → (B.toOver ⟶ B.toOver))
    (hmatrix : ∀ i, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism a (E.map i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism b (k i))
    (htransverse : IsCompl (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b HB).holomorphic
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a (Canonical.Abelian.IntrinsicPeriods.canonicalH1 A)).antiholomorphic) :
    MarkedPeriodClassification.Abelian.IntrinsicPeriods.HasMarkedGroupIso A B a b := by
  let HA := Canonical.Abelian.IntrinsicPeriods.canonicalH1 A
  have hHA : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety HA := Canonical.Abelian.IntrinsicPeriods.canonicalH1_isCanonical A
  let e := (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).baseChange ℚ ℂ _ _
  let W := (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b HB).holomorphic
  let WA := W.comap e.toLinearMap
  have hanti : (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).antiholomorphic.comap e.toLinearMap =
      A.h1Antiholomorphic := by
    ext x
    change (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).toLinearMap.baseChange ℂ x ∈
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).antiholomorphic ↔ _
    rw [MarkedActions.Abelian.IntrinsicPeriods.markedHodge_baseChange_antiholomorphic_iff, hHA.2]
    rfl
  have hWAcompl : IsCompl WA A.h1Antiholomorphic := by
    have h := (Submodule.orderIsoMapComap e).symm.isCompl htransverse
    change IsCompl WA ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).antiholomorphic.comap e.toLinearMap) at h
    rwa [hanti] at h
  have hWA : WA = A.h1Holomorphic := by
    apply E.rigid WA hWAcompl
    intro i x hx
    have hi := MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism_hodge b HB hHB (k i)
    rw [← hmatrix i] at hi
    have he := hi (e x) hx
    change (MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism a (E.map i)).baseChange ℂ
      ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).toLinearMap.baseChange ℂ x) ∈ W at he
    rw [MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism, MarkedActions.Abelian.IntrinsicPeriods.conjugateCoordinates_baseChange] at he
    exact he
  have hmarked : (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).holomorphic =
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b HB).holomorphic := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    change (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).toLinearMap.baseChange ℂ y ∈
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).holomorphic ↔ e y ∈ W
    rw [MarkedActions.Abelian.IntrinsicPeriods.markedHodge_baseChange_holomorphic_iff, hHA.1]
    exact (SetLike.ext_iff.mp hWA y).symm
  exact (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodge_eq_iff_marked_group_iso A B a b HA HB hHA hHB).mp hmarked

theorem fixed_enhancement_marked_equivariant_iso
    {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (E : AlgebraicEnhancement.Abelian.CMEnhancement A) (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A)
    (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (HB : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (B.variety.rationalCohomology 1))
    (hHB : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 B.variety HB)
    (k : Fin E.size → (B.toOver ⟶ B.toOver)) (hk : ∀ i, IsMonHom (k i))
    (hmatrix : ∀ i, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism a (E.map i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism b (k i))
    (htransverse : IsCompl (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b HB).holomorphic
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a (Canonical.Abelian.IntrinsicPeriods.canonicalH1 A)).antiholomorphic) :
    EquivariantRigidity.Abelian.IntrinsicPeriods.HasMarkedEquivariantIso A B a b E.map k :=
  EquivariantRigidity.Abelian.IntrinsicPeriods.hasMarkedEquivariantIso_of_marked_iso a b E.map k E.group hk hmatrix
    (fixed_enhancement_marked_group_iso E a B b HB hHB k hmatrix htransverse)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FixedEnhancementRigidity.Abelian.IntrinsicPeriods
