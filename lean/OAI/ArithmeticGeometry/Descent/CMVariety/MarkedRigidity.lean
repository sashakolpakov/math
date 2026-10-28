import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedActions
import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicEnhancement

/-! # Marked Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.MarkedRigidity.Abelian.IntrinsicPeriods

noncomputable section

/-!
Local rigidity of the actual marked abelian variety with its constructed
finite algebraic CM enhancement. A second actual abelian variety whose
endomorphisms have the same matrices in integral markings, and whose
period is in the transverse chart, is algebraically group-isomorphic to
the CM variety. No classification map or injectivity premise is assumed.

Passing from this result to a neighborhood in an arithmetic moduli scheme
still requires local marked uniformization of an actual abelian family.
-/

open _root_.CategoryTheory

variable {ι : Type} [Fintype ι]

/-- Construct the finite algebraic enhancement and prove uniqueness of
the actual marked abelian variety throughout its transverse period chart. -/
theorem hasCMH1_marked_local_rigidity (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (hCM : A.HasCMH1)
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) :
    ∃ (HA : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)),
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety HA ∧
      ∃ (r : ℕ) (g : Fin r → (A.toOver ⟶ A.toOver)),
        (∀ i, IsMonHom (g i)) ∧
        ∀ (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι B)
          (HB : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (B.variety.rationalCohomology 1)),
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 B.variety HB →
          ∀ k : Fin r → (B.toOver ⟶ B.toOver),
            (∀ i, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism a (g i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism b (k i)) →
            IsCompl (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b HB).holomorphic
              (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).antiholomorphic →
            MarkedPeriodClassification.Abelian.IntrinsicPeriods.HasMarkedGroupIso A B a b := by
  obtain ⟨r, g, hg, _, _, hrigid⟩ := AlgebraicEnhancement.Abelian.hasCMH1_finite_algebraic_enhancement_rigid A hCM
  obtain ⟨HA, hhol, hanti, _⟩ := hCM
  have hHA : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety HA := ⟨hhol, hanti⟩
  refine ⟨HA, hHA, r, g, hg, ?_⟩
  intro B b HB hHB k hmatrix htransverse
  let e := (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).baseChange ℚ ℂ _ _
  let W := (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b HB).holomorphic
  let WA := W.comap e.toLinearMap
  have hanti' : (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).antiholomorphic.comap e.toLinearMap =
      A.h1Antiholomorphic := by
    ext x
    change (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).toLinearMap.baseChange ℂ x ∈
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).antiholomorphic ↔ _
    rw [MarkedActions.Abelian.IntrinsicPeriods.markedHodge_baseChange_antiholomorphic_iff, hanti]
  have hWAcompl : IsCompl WA A.h1Antiholomorphic := by
    have h := (Submodule.orderIsoMapComap e).symm.isCompl htransverse
    change IsCompl WA
      ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).antiholomorphic.comap e.toLinearMap) at h
    rwa [hanti'] at h
  have hWA : WA = A.h1Holomorphic := by
    apply hrigid WA hWAcompl
    intro i x hx
    have hi := MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism_hodge b HB hHB (k i)
    rw [← hmatrix i] at hi
    have he := hi (e x) hx
    change (MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism a (g i)).baseChange ℂ
      ((MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).toLinearMap.baseChange ℂ x) ∈ W at he
    rw [MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism, MarkedActions.Abelian.IntrinsicPeriods.conjugateCoordinates_baseChange] at he
    exact he
  have hmarked : (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).holomorphic =
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure b HB).holomorphic := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    change (MarkedPeriodClassification.Abelian.IntrinsicPeriods.rationalCoordinates a).toLinearMap.baseChange ℂ y ∈
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure a HA).holomorphic ↔ e y ∈ W
    rw [MarkedActions.Abelian.IntrinsicPeriods.markedHodge_baseChange_holomorphic_iff, hhol]
    exact (SetLike.ext_iff.mp hWA y).symm
  exact (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodge_eq_iff_marked_group_iso A B a b HA HB hHA hHB).mp hmarked

end

end OAI.ArithmeticGeometry.Descent.CMVariety.MarkedRigidity.Abelian.IntrinsicPeriods
