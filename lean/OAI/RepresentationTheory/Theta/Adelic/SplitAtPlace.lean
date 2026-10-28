import OAI.RepresentationTheory.Theta.Adelic.SplitLocalSplitting
import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitGaussian
import OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial
import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel

/-! # Split At Place -/

namespace OAI.RepresentationTheory.Theta.Adelic.SplitAtPlace

noncomputable section

/-! The split local construction satisfies the full statement's exact
corrected normalization predicate at every split place. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.LocalKernel.Construction
open OAI.RepresentationTheory.Theta.Adelic.SplitNorm OAI.RepresentationTheory.Theta.Adelic.SplitLocalSplitting OAI.RepresentationTheory.Theta.Adelic.GeneralSplitGaussian

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
variable {n m : ℕ} (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)

theorem split_at_place (hnm : 0 < n * m) (hsq : IsSquare (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d))
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) n m H.val K.val) :
    ∃ s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (n * m) C.ψ v,
      (∀ g, Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (n * m) C.ψ v (s g) = Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g) ∧
      Weil.AdelicSplitting.CorrectedNormalization.Construction.CorrectedLocalNormalization F d hd n m C v H K P s := by
  let dv := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d
  have hdv : dv ≠ 0 := (map_ne_zero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr hd
  obtain ⟨r, hr⟩ := hsq
  have hr2 : r ^ 2 = dv := by simpa only [pow_two] using hr.symm
  have hr0 : r ≠ 0 := by intro hz; apply hdv; simpa [hz] using hr2.symm
  have hc := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous v
  have hu := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary v
  have hn := FiniteCharacterNontrivial.local_character_nontrivial F C.ψ C.ψ_continuous
    C.ψ_unitary C.ψ_nontrivial C.ψ_principal v
  have hV : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ, Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χV v
      (Units.map (algebraMap (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) dv)).toMonoidHom a) = 1 := by
    intro a
    change Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χV v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a) = 1
    rw [C.χV_restriction, SplitNorm.normCharacter_split F d v r hr2 hr0, one_pow]
  have hW : ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ, Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χW v
      (Units.map (algebraMap (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) dv)).toMonoidHom a) = 1 := by
    intro a
    change Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χW v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a) = 1
    rw [C.χW_restriction, SplitNorm.normCharacter_split F d v r hr2 hr0, one_pow]
  have hWeil := GeneralSplitGaussian.schrodingerWeilConstant_split (Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F v)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ v) hc hu hn dv hdv (show IsSquare dv from ⟨r, hr⟩)
  change Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ v)
    (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) = 1 at hWeil
  obtain ⟨s, hp, hfirst, hsecond⟩ := SplitLocalSplitting.split_local_splitting hdv r hr2 hr0 n m hnm H K hH hK P
    (Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χV v) (Weil.AdelicSplitting.Characters.Construction.localCharacter F d C.χW v) hV hW
    (Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ v) hc hu hn
  refine ⟨s, hp, ?_, ?_⟩
  · intro g u hgu f h
    simp only [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedFirstFactorScalar, hWeil, SplitNorm.normCharacterScalar_split F d v r hr2 hr0,
      Circle.coe_one, inv_one, one_pow, one_mul]
    exact hfirst g u hgu f h
  · intro g u hgu f h
    simp only [Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedSecondFactorScalar, hWeil, SplitNorm.normCharacterScalar_split F d v r hr2 hr0,
      Circle.coe_one, inv_one, one_pow, one_mul]
    exact hsecond g u hgu f h

end

end OAI.RepresentationTheory.Theta.Adelic.SplitAtPlace
