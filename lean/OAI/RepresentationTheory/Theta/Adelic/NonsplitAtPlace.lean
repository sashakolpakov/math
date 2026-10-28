import OAI.RepresentationTheory.Theta.Adelic.NonsplitLocalSplitting
import OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel

/-! # Nonsplit At Place -/

namespace OAI.RepresentationTheory.Theta.Adelic.NonsplitAtPlace

noncomputable section

/-! The nonsplit nonarchimedean construction satisfies the exact local
normalization predicate of the full AdelicTheta statement. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel.Construction
open OAI.RepresentationTheory.Theta.Adelic.FixedDeterminant OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
variable {n m : ℕ} (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)

theorem normCharacterScalar_fixed_unit
    (z : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ) (hz : star z = z) :
    Weil.AdelicSplitting.Normalization.Construction.normCharacterScalar F d v z.val.re =
      QuadraticNormCharacter.normSign (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) (FixedDeterminant.scalarReUnit (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) z hz) := by
  rw [Weil.AdelicSplitting.Normalization.Construction.normCharacterScalar, dite_eq_left (FixedDeterminant.fixedUnit_re_ne_zero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) z hz)]
  rfl

theorem nonsplit_at_place [IsUltrametricDist (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)]
    (hns : ¬ IsSquare (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d))
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) n m H.val K.val) :
    ∃ s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (n * m) C.ψ v,
      (∀ g, Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (n * m) C.ψ v (s g) = Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g) ∧
      Weil.AdelicSplitting.CorrectedNormalization.Construction.CorrectedLocalNormalization F d hd n m C v H K P s := by
  let dv := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d
  have hdv : dv ≠ 0 := (map_ne_zero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr hd
  let bH := FixedDeterminant.scalarReUnit dv (Matrix.GeneralLinearGroup.det H) (FixedDeterminant.hermitian_det_fixed dv H hH)
  let bK := FixedDeterminant.scalarReUnit dv ((Weil.AdelicSplitting.Normalization.Construction.localDelta F d hd v)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K)
    (FixedDeterminant.skew_det_fixed dv hdv K hK)
  have hbH : QuadraticNormSquareQuotient.scalarUnits dv bH = Matrix.GeneralLinearGroup.det H :=
    FixedDeterminant.scalarUnits_scalarReUnit dv _ (FixedDeterminant.hermitian_det_fixed dv H hH)
  have hbK : QuadraticNormSquareQuotient.scalarUnits dv bK = (Weil.AdelicSplitting.Normalization.Construction.deltaUnit dv hdv)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K :=
    FixedDeterminant.scalarUnits_scalarReUnit dv _ (FixedDeterminant.skew_det_fixed dv hdv K hK)
  have hV : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ,
      Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χV v (QuadraticNormSquareQuotient.scalarUnits dv a) = QuadraticNormCharacter.normSign dv a ^ n := C.χV_restriction v
  have hW : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ,
      Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χW v (QuadraticNormSquareQuotient.scalarUnits dv a) = QuadraticNormCharacter.normSign dv a ^ m := C.χW_restriction v
  obtain ⟨s, hs, hfirst, hsecond⟩ := NonsplitLocalSplitting.nonsplit_local_splitting
    dv hdv hns (Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F v) H K hH hK P (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ v)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous v)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary v)
    (FiniteCharacterNontrivial.local_character_nontrivial F C.ψ C.ψ_continuous
      C.ψ_unitary C.ψ_nontrivial C.ψ_principal v)
    (Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χV v) (Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χW v) hV hW bH bK hbH hbK
  have hnormH : Weil.AdelicSplitting.Normalization.Construction.normCharacterScalar F d v (Matrix.GeneralLinearGroup.det H).val.re = QuadraticNormCharacter.normSign dv bH :=
    normCharacterScalar_fixed_unit F d v _ (FixedDeterminant.hermitian_det_fixed dv H hH)
  have hnormK : Weil.AdelicSplitting.Normalization.Construction.normCharacterScalar F d v
      ((Weil.AdelicSplitting.Normalization.Construction.localDelta F d hd v)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K).val.re = QuadraticNormCharacter.normSign dv bK :=
    normCharacterScalar_fixed_unit F d v _ (FixedDeterminant.skew_det_fixed dv hdv K hK)
  refine ⟨s, hs, ?_, ?_⟩
  · intro g u hDiff f h
    rw [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedFirstFactorScalar, hnormK]
    exact hfirst g u hDiff f h
  · intro g u hDiff f h
    rw [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedSecondFactorScalar, hnormH]
    exact hsecond g u hDiff f h

end

end OAI.RepresentationTheory.Theta.Adelic.NonsplitAtPlace
