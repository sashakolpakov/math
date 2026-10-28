import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionOrbit
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Reflection Continuity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionContinuity

noncomputable section

/-! Continuity of the actual rank-three reflection formula and approximation
of its negative-unit orbits by any dense set of reflection vectors. Arithmetic
density and finite-prime congruence conditions remain separate obligations.
-/

open scoped _root_.Topology

variable (B : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) →ₛₗ[starRingEnd ℂ] ℂ)

def complexPairingFunctional (y : Fin 3 → ℂ) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun x := B x y
  map_add' x z := by simp only [map_add, LinearMap.add_apply]
  map_smul' a x := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply]

theorem continuous_complexPairing_left (y : Fin 3 → ℂ) : Continuous (fun x => B x y) :=
  (complexPairingFunctional B y).continuous_of_finiteDimensional

theorem continuous_complexPairing_right
    (hB : ∀ x y, B x y = star (B y x)) (y : Fin 3 → ℂ) :
    Continuous (fun x => B y x) :=
  (continuous_star.comp (continuous_complexPairing_left B y)).congr
    (fun x => (hB y x).symm)

theorem continuous_complexPairing_diagonal
    (hB : ∀ x y, B x y = star (B y x)) : Continuous (fun x => B x x) := by
  have hsum : Continuous (fun v : Fin 3 → ℂ =>
      ∑ i, v i * B (Pi.single i 1) v) :=
    continuous_finsetSum _ (fun i _ =>
      (continuous_apply i).mul (continuous_complexPairing_right B hB (Pi.single i 1)))
  apply hsum.congr
  intro v
  exact ReflectionDeterminant.linearFunctional_single_sum (complexPairingFunctional B v) v

/-- The formula is defined everywhere; it agrees with the constructed
reflection whenever its reflection vector is nonisotropic. -/
def complexReflectionValue (x v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  x - (2 * (B x v / B v v)) • v

theorem complexReflectionValue_eq (x v : Fin 3 → ℂ) (hv : B v v ≠ 0) :
    complexReflectionValue B x v = Hermitian.Reflection.hermitianReflection (starRingEnd ℂ) B v hv x := rfl

theorem continuousAt_complexReflectionValue
    (hB : ∀ x y, B x y = star (B y x)) (x v : Fin 3 → ℂ) (hv : B v v ≠ 0) :
    ContinuousAt (complexReflectionValue B x) v := by
  have hs : ContinuousAt (fun a => (2 : ℂ) * (B x a / B a a)) v :=
    continuousAt_const.mul
      ((continuous_complexPairing_right B hB x).continuousAt.div
        (continuous_complexPairing_diagonal B hB).continuousAt hv)
  have hi : ContinuousAt (fun a : Fin 3 → ℂ => a) v := continuousAt_id
  exact continuousAt_const.sub (hs.smul hi)

theorem exists_dense_reflection_vector_in_orbit_neighborhood
    (hB : ∀ x y, B x y = star (B y x))
    (D : Set (Fin 3 → ℂ)) (hD : Dense D)
    (w : Fin 3 → ℂ) (hw : B w w ≠ 0)
    (x y : Fin 3 → ℂ) (hx : B x x = -1) (hy : B y y = -1)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U)
    (hyU : ∀ u : ℂ, ‖u‖ = 1 → u • y ∈ U) :
    ∃ v ∈ D, ∃ hv : B v v ≠ 0,
      ReflectionDeterminant.twoHermitianReflections (starRingEnd ℂ) B v w hv hw x ∈ U := by
  obtain ⟨u, hu, v, hv, hmove, _, _⟩ :=
    ReflectionOrbit.exists_two_reflections_between_negative_unit_vectors B hB w hw x y hx hy
  let z := Hermitian.Reflection.hermitianReflection (starRingEnd ℂ) B w hw x
  have hhit : complexReflectionValue B z v ∈ U := by
    change ReflectionDeterminant.twoHermitianReflections (starRingEnd ℂ) B v w hv hw x ∈ U
    rw [hmove]
    exact hyU u hu
  have hnoniso : {a | B a a ≠ 0} ∈ 𝓝 v :=
    (isOpen_ne_fun (continuous_complexPairing_diagonal B hB) continuous_const).mem_nhds hv
  have hpre : (complexReflectionValue B z) ⁻¹' U ∈ 𝓝 v :=
    (continuousAt_complexReflectionValue B hB z v hv).preimage_mem_nhds
      (hU.mem_nhds hhit)
  obtain ⟨W, hWsub, hW, hvW⟩ := mem_nhds_iff.mp (Filter.inter_mem hnoniso hpre)
  obtain ⟨a, haD, haW⟩ := hD.exists_mem_open hW ⟨v, hvW⟩
  obtain ⟨ha, hUa⟩ := hWsub haW
  exact ⟨a, haD, ha, hUa⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionContinuity
