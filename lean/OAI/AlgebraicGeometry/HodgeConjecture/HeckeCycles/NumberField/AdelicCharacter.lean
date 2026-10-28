import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteCharacter
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArchimedeanTrace

/-! # Adelic Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.AdelicCharacter.CM

noncomputable section

/-! An actual continuous unitary character of the number-field adeles,
trivial on the principal field and nontrivial globally. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
variable (F : Type) [Field F] [NumberField F]

def character : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ where
  toFun x := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.trace F x.1) *
    FiniteCharacter.CM.character F x.2
  map_zero_eq_one' := by
    change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.trace F 0) * FiniteCharacter.CM.character F 0 = 1
    rw [map_zero, AddChar.map_zero_eq_one, AddChar.map_zero_eq_one, one_mul]
  map_add_eq_mul' x y := by
    change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.trace F (x.1 + y.1)) *
      FiniteCharacter.CM.character F (x.2 + y.2) = _
    rw [map_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring

theorem character_apply (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) : character F x =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.trace F x.1) * FiniteCharacter.CM.character F x.2 := rfl

theorem character_continuous : Continuous (character F : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F → ℂ) := by
  have hr : Continuous (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter : ℝ → ℂ) :=
    continuous_subtype_val.comp Real.continuous_fourierChar
  exact (hr.comp ((ArchimedeanTrace.CM.trace_continuous F).comp continuous_fst)).mul
    ((FiniteCharacter.CM.character_continuous F).comp continuous_snd)

theorem character_unitary (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) : ‖character F x‖ = 1 := by
  rw [character_apply, norm_mul, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_unitary,
    FiniteCharacter.CM.character_unitary, one_mul]

theorem character_rational (q : F) : character F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1 := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.trace F (algebraMap F (InfiniteAdeleRing F) q)) *
    FiniteCharacter.CM.character F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) q) = 1
  rw [ArchimedeanTrace.CM.trace_rational, FiniteCharacter.CM.character_rational,
    ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

theorem mixed_character (x : mixedEmbedding.mixedSpace F) :
    character F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.mixedTrace F x) := by
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.trace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x)) * FiniteCharacter.CM.character F 0 = _
  rw [AddChar.map_zero_eq_one, mul_one]
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (ArchimedeanTrace.CM.mixedTrace F
    (InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x))) = _
  rw [RingEquiv.apply_symm_apply]

theorem trace_one : ArchimedeanTrace.CM.mixedTrace F (mixedEmbedding F 1) = (Module.finrank ℚ F : ℝ) := by
  rw [ArchimedeanTrace.CM.mixedTrace_rational]
  have ht : Algebra.trace ℚ F (1 : F) = (Module.finrank ℚ F : ℚ) := by
    simpa using Algebra.trace_algebraMap (R := ℚ) (S := F) (1 : ℚ)
  rw [ht, Rat.cast_natCast]

theorem character_nontrivial : ∃ x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F, character F x ≠ 1 := by
  let n : ℝ := Module.finrank ℚ F
  have hn : n ≠ 0 := by
    change (Module.finrank ℚ F : ℝ) ≠ 0
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  let y := (1 / (2 * n)) • mixedEmbedding F 1
  refine ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0), ?_⟩
  rw [mixed_character]
  have hy : ArchimedeanTrace.CM.mixedTrace F y = (1 / 2 : ℝ) := by
    dsimp only [y]
    rw [map_smul, trace_one]
    change (1 / (2 * n)) * n = 1 / 2
    field_simp
  rw [hy]
  intro he
  obtain ⟨m, hm⟩ := (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.standardRealCharacter_eq_one_iff _).mp he
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (m : ℝ) < 1 := by linarith
  have hz : (0 : ℤ) < m := by exact_mod_cast hm0
  have ho : m < (1 : ℤ) := by exact_mod_cast hm1
  omega

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.AdelicCharacter.CM
