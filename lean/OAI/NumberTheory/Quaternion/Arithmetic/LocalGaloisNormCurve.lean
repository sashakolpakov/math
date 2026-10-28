import OAI.NumberTheory.Quaternion.Arithmetic.MappedWeightCurves
import OAI.NumberTheory.Quaternion.Arithmetic.ProductCurveDerivative
import OAI.NumberTheory.Quaternion.Arithmetic.GaloisTraceMatrix

/-! # Local Galois Norm Curve -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalGaloisNormCurve

noncomputable section

section

/-! A local curve obtained by multiplying all Galois conjugates of
an integer-weight curve. Its derivative is the entrywise field trace. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {F E K A : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  [NontriviallyNormedField K] [NormedCommRing A] [Algebra F A] [NormedAlgebra K A]
  [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] {n : ℕ}

def localGaloisNormCurve (f : E →ₐ[F] A) (B : Matrix.SpecialLinearGroup (Fin n) E)
    (a : E) (m : Fin n → ℤ) (t : K) : Matrix (Fin n) (Fin n) A :=
  ((Finset.univ : Finset (E ≃ₐ[F] E)).toList.map
    (fun σ => MappedWeightCurves.mappedWeightCurve (f.comp σ.toAlgHom).toRingHom B a m t)).prod

omit [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] in
theorem localGaloisNormCurve_zero (f : E →ₐ[F] A) (B : Matrix.SpecialLinearGroup (Fin n) E)
    (a : E) (m : Fin n → ℤ) : localGaloisNormCurve (K := K) f B a m 0 = 1 := by
  apply List.prod_eq_one
  intro X hX
  obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hX
  exact MappedWeightCurves.mappedWeightCurve_zero _ _ _ _

theorem localGaloisNormCurve_hasDerivAt [IsGalois F E]
    (f : E →ₐ[F] A) (B : Matrix.SpecialLinearGroup (Fin n) E) (a : E) (m : Fin n → ℤ) :
    HasDerivAt (localGaloisNormCurve (K := K) f B a m)
      ((GaloisTraceMatrix.fieldTraceMatrix (F := F) (a • MappedWeightCurves.integerWeightMatrix B m)).map (algebraMap F A)) 0 := by
  have h := ProductCurveDerivative.list_curve_prod_hasDerivAt_one (K := K)
    (Finset.univ : Finset (E ≃ₐ[F] E)).toList
    (fun σ => MappedWeightCurves.mappedWeightCurve (K := K) (f.comp σ.toAlgHom).toRingHom B a m)
    (fun σ => (a • MappedWeightCurves.integerWeightMatrix B m).map (f.comp σ.toAlgHom)) 0
    (fun σ _ => MappedWeightCurves.mappedWeightCurve_hasDerivAt _ _ _ _)
    (fun σ _ => MappedWeightCurves.mappedWeightCurve_zero _ _ _ _)
  rw [Finset.sum_map_toList, ← GaloisTraceMatrix.mapped_fieldTraceMatrix] at h
  exact h

end

/-! Continuity of the local norm curve on its open unit domain. -/

open scoped Classical _root_.Matrix.Norms.Operator
open Filter _root_.Topology

variable {K A : Type*} [NontriviallyNormedField K] [NormedCommRing A]
  [NormedAlgebra K A] [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] {n : ℕ}

omit [CompleteSpace K] [FiniteDimensional K A] in
theorem unitPower_continuousAt {x : A} (hx : IsUnit x) (m : ℤ) :
    ContinuousAt (fun y => LocalUnitPowers.unitPower y m) x := by
  obtain ⟨u, rfl⟩ := hx
  cases m with
  | ofNat k => exact continuousAt_id.pow k
  | negSucc k => exact (NormedRing.inverse_continuousAt u).pow (k + 1)

theorem localWeightCurve_continuousAt (B C : Matrix (Fin n) (Fin n) A)
    (a : A) (m : Fin n → ℤ) {t : K} (ht : IsUnit (1 + t • a)) :
    ContinuousAt (LocalWeightCurves.localWeightCurve (K := K) B C a m) t := by
  let d : (Fin n → A) →L[K] Matrix (Fin n) (Fin n) A :=
    (Matrix.diagonalLinearMap (Fin n) K A).toContinuousLinearMap
  have ha : ContinuousAt (fun t : K => 1 + t • a) t :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hp : ContinuousAt (fun t : K => fun i => LocalUnitPowers.unitPower (1 + t • a) (m i)) t :=
    continuousAt_pi.mpr (fun i => (unitPower_continuousAt ht (m i)).comp
      (f := fun t : K => 1 + t • a) ha)
  exact (continuousAt_const.mul (d.continuous.continuousAt.comp hp)).mul continuousAt_const

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra F A]

theorem localGaloisNormCurve_continuousAt (f : E →ₐ[F] A)
    (B : Matrix.SpecialLinearGroup (Fin n) E) (a : E) (m : Fin n → ℤ) {t : K}
    (ht : ∀ σ : E ≃ₐ[F] E, IsUnit (1 + t • f (σ a))) :
    ContinuousAt (localGaloisNormCurve (K := K) f B a m) t := by
  apply tendsto_list_prod
  intro σ _
  exact localWeightCurve_continuousAt _ _ _ _ (ht σ)

omit [CompleteSpace K] [FiniteDimensional K A] in
theorem localGaloisNormCurve_unitDomain_isOpen (f : E →ₐ[F] A) (a : E) :
    IsOpen {t : K | ∀ σ : E ≃ₐ[F] E, IsUnit (1 + t • f (σ a))} := by
  have he : {t : K | ∀ σ : E ≃ₐ[F] E, IsUnit (1 + t • f (σ a))} =
      ⋂ σ : E ≃ₐ[F] E, (fun t : K => 1 + t • f (σ a)) ⁻¹' {x : A | IsUnit x} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [he]
  exact isOpen_iInter_of_finite (fun σ => Units.isOpen.preimage
    (continuous_const.add (continuous_id.smul continuous_const)))

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalGaloisNormCurve
