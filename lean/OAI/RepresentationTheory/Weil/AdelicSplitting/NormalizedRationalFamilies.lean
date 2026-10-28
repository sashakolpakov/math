import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalWeakTheta
import OAI.RepresentationTheory.Weil.AdelicSplitting.AnyRankFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedScalarProducts
import OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange

/-! # Normalized Rational Families -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizedRationalFamilies.Construction

noncomputable section

section

/-! The actual rational unitary operator family and the analytic
comparison hypotheses discharged from the original AdelicSplitting local inputs. -/

open Filter _root_.MeasureTheory
open scoped Classical _root_.NumberField ComplexConjugate

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

def normalizedRationalFamily (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) : Rational.Construction.RestrictedCover F (n * m) C.ψ :=
  ⟨fun v => D.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v g), by
    filter_upwards [D.unramified, Integral.Construction.rationalPairLocal_integral F H.val K.val g] with v hv hg
    exact hv hg⟩

theorem normalizedRationalFamily_assemble (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :
    Rational.Construction.assembleGlobalCover F (n * m) C.ψ (normalizedRationalFamily F d hd n m H K C P D g) =
      Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) := rfl

theorem normalizedRationalFamily_covers (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F (n * m) C.ψ v (normalizedRationalFamily F d hd n m H K C P D g v) =
      Vacuum.Construction.rationalSymplecticLocal F (n * m) v (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g) := by
  change Vacuum.Construction.projectionAt F (n * m) C.ψ v (D.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v g)) = _
  rw [D.covers, BaseChange.Construction.localDualAction_rational]

include D in
theorem normalized_weak_family_positive (hns : ¬ IsSquare d) (hN : 0 < n * m)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (a : Rational.Construction.RestrictedCover F (n * m) C.ψ) (γ : Local.FunctionsMetaplectic.Construction.Symplectic F (n * m))
    (c : ArchimedeanAdeles.Construction.Places F → ℂ) (hcprod : HasProd c 1)
    (hnorm : ∀ v (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m)),
      (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v) (a v) f).val x * conj (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) =
      c v * CorrectedNormalization.Construction.correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
        (Vacuum.Construction.rationalSymplecticLocal F (n * m) v γ) f.val h.val) : a ∈ TestFamilyAction.Construction.positiveThetaSubgroup F (n * m) C.ψ := by
  apply RationalWeakTheta.Construction.rational_weak_normalization_positive F (n * m) C.ψ C.ψ_continuous C.ψ_unitary C.ψ_principal
    (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D)
    (fun v => NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D v hN)
    (RationalFourier.Construction.rationalFourierFamily F d hd hns n m hN H K hH hK C P D)
    (RationalFourier.Construction.rationalFourierFamily_spec F d hd hns n m hN H K hH hK C P D)
    (AnyRankFourier.Construction.anyRankRationalFourierFamily F d hd n m hN H K C P D (n * m + n * m) hns hH hK)
    (AnyRankFourier.Construction.anyRankRationalFourierFamily_spec F d hd n m hN H K C P D (n * m + n * m) hns hH hK)
    a γ c hcprod hnorm

end

/-! The two prescribed unitary open-cell normalizations give positive
theta multipliers for their actual restricted rational operator families. -/

open _root_.MeasureTheory
open scoped Classical _root_.NumberField ComplexConjugate

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include hns hN hH hK in
theorem normalized_firstFactor_positive (g : UnitaryBase.Construction.Unitary H.val) (hopen : IsUnit (g.val.val - 1)) :
    normalizedRationalFamily F d hd n m H K C P D (g, 1) ∈ TestFamilyAction.Construction.positiveThetaSubgroup F (n * m) C.ψ := by
  obtain ⟨u, hu⟩ := hopen
  let c (v : ArchimedeanAdeles.Construction.Places F) := CorrectedNormalization.Construction.correctedFirstFactorScalar F d hd n m C v
    (Assembly.Construction.localizedUnit F d H v) (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v)
  apply normalized_weak_family_positive F d hd n m H K C P D hns hN hH hK
    _ (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (g, 1)) c
    ((CorrectedScalarProducts.Construction.normalized_corrected_scalar_products F d hd hns n m hN H K hH hK C P D).1 u)
  intro v f h
  have hlocal : (Assembly.Construction.localizedUnit F d u v).val =
      (Integral.Construction.rationalUnitaryLocal F H.val v g).val.val - 1 := by
    change u.val.map (Integral.Construction.rationalQuadraticLocal F d v) = g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - 1
    rw [hu]
    exact map_sub (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix _ _ |>.trans
      (congrArg (g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - ·)
        (map_one (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix))
  have he := (D.normalization v).1 (Integral.Construction.rationalUnitaryLocal F H.val v g)
    (Assembly.Construction.localizedUnit F d u v) hlocal f h
  have hdual : TensorSpace.Construction.dualPairSymplectic (Assembly.Construction.localizedUnit F d H v).val (Assembly.Construction.localizedUnit F d K v).val
      (P.localFrame v) (Integral.Construction.rationalUnitaryLocal F H.val v g, 1) =
      Vacuum.Construction.rationalSymplecticLocal F (n * m) v (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (g, 1)) := by
    have ht := BaseChange.Construction.localDualAction_rational F d n m H K P v (g, 1)
    change TensorSpace.Construction.dualPairSymplectic _ _ _ (Integral.Construction.rationalUnitaryLocal F H.val v g, Integral.Construction.rationalUnitaryLocal F K.val v 1) = _ at ht
    simpa only [map_one] using! ht
  rw [hdual] at he
  change (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
    (D.atPlace v (Integral.Construction.rationalUnitaryLocal F H.val v g, Integral.Construction.rationalUnitaryLocal F K.val v 1)) f).val x * conj (h.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) = _
  rw [map_one]
  exact he

include hns hN hH hK in
theorem normalized_secondFactor_positive (g : UnitaryBase.Construction.Unitary K.val) (hopen : IsUnit (g.val.val - 1)) :
    normalizedRationalFamily F d hd n m H K C P D (1, g) ∈ TestFamilyAction.Construction.positiveThetaSubgroup F (n * m) C.ψ := by
  obtain ⟨u, hu⟩ := hopen
  let c (v : ArchimedeanAdeles.Construction.Places F) := CorrectedNormalization.Construction.correctedSecondFactorScalar F d n m C v
    (Assembly.Construction.localizedUnit F d H v) (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v)
  apply normalized_weak_family_positive F d hd n m H K C P D hns hN hH hK
    _ (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (1, g)) c
    ((CorrectedScalarProducts.Construction.normalized_corrected_scalar_products F d hd hns n m hN H K hH hK C P D).2 u)
  intro v f h
  have hlocal : (Assembly.Construction.localizedUnit F d u v).val =
      (Integral.Construction.rationalUnitaryLocal F K.val v g).val.val - 1 := by
    change u.val.map (Integral.Construction.rationalQuadraticLocal F d v) = g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - 1
    rw [hu]
    exact map_sub (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix _ _ |>.trans
      (congrArg (g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - ·)
        (map_one (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix))
  have he := (D.normalization v).2 (Integral.Construction.rationalUnitaryLocal F K.val v g)
    (Assembly.Construction.localizedUnit F d u v) hlocal f h
  have hdual : TensorSpace.Construction.dualPairSymplectic (Assembly.Construction.localizedUnit F d H v).val (Assembly.Construction.localizedUnit F d K v).val
      (P.localFrame v) (1, Integral.Construction.rationalUnitaryLocal F K.val v g) =
      Vacuum.Construction.rationalSymplecticLocal F (n * m) v (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (1, g)) := by
    have ht := BaseChange.Construction.localDualAction_rational F d n m H K P v (1, g)
    change TensorSpace.Construction.dualPairSymplectic _ _ _ (Integral.Construction.rationalUnitaryLocal F H.val v 1, Integral.Construction.rationalUnitaryLocal F K.val v g) = _ at ht
    simpa only [map_one] using! ht
  rw [hdual] at he
  change (∫ x, (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
    (D.atPlace v (Integral.Construction.rationalUnitaryLocal F H.val v 1, Integral.Construction.rationalUnitaryLocal F K.val v g)) f).val x * conj (h.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) = _
  rw [map_one]
  exact he

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizedRationalFamilies.Construction
