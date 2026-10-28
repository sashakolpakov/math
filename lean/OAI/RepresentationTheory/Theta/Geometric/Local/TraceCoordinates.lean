import OAI.RepresentationTheory.Theta.Geometric.JointRationalCompletion
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.TensorProductProductFormulas

/-! # Trace Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The original rational trace is the sum of the supplied split local
characters, and their opposite indices are actual CM conjugates. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.localEmbedding_conjugate (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (v : Fin s × Bool) (a : E) :
    D.localEmbedding (v.1, !v.2) a =
      D.localEmbedding v (NumberField.IsCMField.complexConj E a) := by
  have he : D.localEmbedding (v.1, !v.2) = (D.localEmbedding v).comp
      (NumberField.IsCMField.complexConj E).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers E)
    intro x
    change D.localEmbedding (v.1, !v.2) (x : E) =
      D.localEmbedding v (NumberField.IsCMField.ringOfIntegersComplexConj E x : NumberField.RingOfIntegers E)
    rw [hc.1, hc.1, hgood.2.1]
  exact RingHom.congr_fun he a

theorem Data.ActiveHeckeThetaData.rationalTrace_local_sum (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s) (a : E) :
    algebraMap ℚ ℚ_[q] (Algebra.trace ℚ E a) = ∑ v, D.localEmbedding v a := by
  have h := NumberTheory.PadicHodge.WeakAdmissibility.TensorProductProductFormulas.ValuationTheory.Completion.baseChange_pi_trace_eq_sum
    (fun _ : Fin s × Bool => ℚ_[q]) (D.pel.rationalCompletionEquiv hgood hdegree) a
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro v _
  change Algebra.trace ℚ_[q] ℚ_[q] (1 * D.pel.rationalLocalCharacter v a) = D.localEmbedding v a
  rw [one_mul, Algebra.trace_self_apply, D.localEmbedding_eq_rationalLocalCharacter hc]
  rfl

end

/-! The prescribed trace polarization in all split local coordinates,
including the conjugate coordinate in its second argument. -/

open scoped BigOperators

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.localCoordinate (v : Fin s × Bool) (i : Fin 3) :
    (Fin s × Bool → Fin 3 → ℚ_[q]) →ₗ[ℚ_[q]] ℚ_[q] :=
  (LinearMap.proj i : (Fin 3 → ℚ_[q]) →ₗ[ℚ_[q]] ℚ_[q]).comp
    (LinearMap.proj v : (Fin s × Bool → Fin 3 → ℚ_[q]) →ₗ[ℚ_[q]] (Fin 3 → ℚ_[q]))

def Data.ActiveHeckeThetaData.localTraceCoefficient (v : Fin s × Bool) (i : Fin 3) : ℚ_[q] :=
  (D.pel.reference.denominator : ℚ_[q]) * D.localEmbedding v D.pel.reference.imaginaryScalar *
    (if i = 2 then D.localEmbedding v D.pel.reference.b else 1)

def Data.ActiveHeckeThetaData.localTracePairing : LinearMap.BilinForm ℚ_[q] (Fin s × Bool → Fin 3 → ℚ_[q]) :=
  ∑ v, ∑ i, D.localTraceCoefficient v i •
    (LinearMap.mul ℚ_[q] ℚ_[q]).compl₁₂ (Data.ActiveHeckeThetaData.localCoordinate v i) (Data.ActiveHeckeThetaData.localCoordinate (v.1, !v.2) i)

theorem Data.ActiveHeckeThetaData.localTracePairing_apply (x y : Fin s × Bool → Fin 3 → ℚ_[q]) :
    D.localTracePairing x y =
      ∑ v, ∑ i, D.localTraceCoefficient v i * x v i * y (v.1, !v.2) i := by
  simp [Data.ActiveHeckeThetaData.localTracePairing, Data.ActiveHeckeThetaData.localCoordinate, mul_assoc]

theorem Data.ActiveHeckeThetaData.localTracePairing_reference (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    D.localTracePairing (D.jointLocalEmbedding x) (D.jointLocalEmbedding y) =
      algebraMap ℚ ℚ_[q] (D.pel.reference.traceForm x y) := by
  rw [Data.ActiveHeckeThetaData.localTracePairing_apply]
  change (∑ v, ∑ i, D.localTraceCoefficient v i * D.localEmbedding v (x i) *
      D.localEmbedding (v.1, !v.2) (y i)) =
    algebraMap ℚ ℚ_[q] ((D.pel.reference.denominator : ℚ) *
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian D.pel.reference.b x y))
  rw [map_mul, map_natCast, D.rationalTrace_local_sum hc hgood hdegree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, map_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_mul, ← D.localEmbedding_conjugate hc hgood]
  by_cases hi : i = 2
  · simp only [Data.ActiveHeckeThetaData.localTraceCoefficient, hi, ite_true]
    ring
  · simp only [Data.ActiveHeckeThetaData.localTraceCoefficient, hi, ite_false, map_one]
    ring

end

end OAI.RepresentationTheory.Theta.Geometric
