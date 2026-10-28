import OAI.NumberTheory.Adeles.LocalCompletions

/-! # Local Norms -/

namespace OAI.NumberTheory.Adeles.LocalNorms.CompletionFactors

noncomputable section

/-! Actual algebraic norms on the local completion extensions. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology

/-- Continuity of the determinant norm on a finite extension of complete normed fields. -/
theorem continuous_algebraNorm
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedField L] [Algebra K L] [ContinuousSMul K L] [FiniteDimensional K L] :
    Continuous (Algebra.norm K (S := L)) := by
  let b := Module.finBasis K L
  have hm : Continuous (Algebra.leftMulMatrix b) :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  convert hm.matrix_det using 1
  ext x
  exact Algebra.norm_eq_matrix_det b x

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

section Finite

open scoped OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver Valued

variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The canonical relative field norm at a finite place. -/
def finiteLocalNorm : w.adicCompletion E →* v.adicCompletion F :=
  Algebra.norm (v.adicCompletion F)

theorem continuous_finiteLocalNorm : Continuous (finiteLocalNorm v w) :=
  continuous_algebraNorm (K := v.adicCompletion F) (L := w.adicCompletion E)

def finiteLocalIdeleNorm : (w.adicCompletion E)ˣ →ₜ* (v.adicCompletion F)ˣ where
  toMonoidHom := Units.map (finiteLocalNorm v w)
  continuous_toFun := Continuous.units_map _ (continuous_finiteLocalNorm v w)

end Finite

@[instance_reducible]
def infiniteCompletionNontriviallyNormedField (v : InfinitePlace F) :
    NontriviallyNormedField v.Completion := {
  (inferInstance : NormedField v.Completion) with
  non_trivial := by
    refine ⟨algebraMap F v.Completion 2, ?_⟩
    change 1 < ‖((WithAbs.equiv v.1).symm (2 : F) : v.Completion)‖
    rw [InfinitePlace.Completion.norm_coe]
    change 1 < v (2 : F)
    rw [show (2 : F) = (2 : ℕ) from rfl, v.map_natCast]
    norm_num
}

open scoped _root_.NumberField.LiesOver

variable (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v]

omit [NumberField F] [NumberField E] in
theorem infiniteCompletion_finiteDimensional : FiniteDimensional v.Completion w.Completion := by
  apply Module.finite_of_finrank_pos
  rcases w.isUnramified_or_isRamified F with h | h
  · rw [h.finrank_eq_one v]
    decide
  · rw [h.finrank_eq_two v]
    decide

/-- The canonical relative field norm at an infinite place. -/
def infiniteLocalNorm : w.Completion →* v.Completion := Algebra.norm v.Completion

omit [NumberField F] [NumberField E] in
theorem continuous_infiniteLocalNorm : Continuous (infiniteLocalNorm v w) :=
  letI := infiniteCompletionNontriviallyNormedField v
  letI := infiniteCompletion_finiteDimensional v w
  continuous_algebraNorm (K := v.Completion) (L := w.Completion)

def infiniteLocalIdeleNorm : w.Completionˣ →ₜ* v.Completionˣ where
  toMonoidHom := Units.map (infiniteLocalNorm v w)
  continuous_toFun := Continuous.units_map _ (continuous_infiniteLocalNorm v w)

end

end OAI.NumberTheory.Adeles.LocalNorms.CompletionFactors
