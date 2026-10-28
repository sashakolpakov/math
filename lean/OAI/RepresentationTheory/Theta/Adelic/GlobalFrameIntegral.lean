import OAI.RepresentationTheory.Theta.Adelic.IntegralFrameCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange

/-! # Global Frame Integral -/

namespace OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral

noncomputable section

/-! Compatibility with one rational frame forces both directions of
the actual local frames to preserve the standard integral lattices at
almost every place. -/

open Filter
open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange.Construction OAI.RepresentationTheory.Theta.Adelic.IntegralFrameCoordinates OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)

structure IntegralFrameAt (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : Prop where
  toPhase : ∀ x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) n m,
    (∀ j, x j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) → ∀ i, (P.localFrame v).coordinates x i ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v
  fromPhase : ∀ x : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) n m,
    (∀ i, x i ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) → ∀ j, (P.localFrame v).coordinates.symm x j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v

theorem rational_tensor_single (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (j : Fin n × Fin m) (a : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) :
    (fun i => Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v ((Pi.single j a : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) i)) =
      Pi.single j (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v a) := by
  funext i
  by_cases h : i = j
  · subst i; simp
  · simp [Pi.single_eq_of_ne h]

theorem rational_phase_single (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (j : Fin (n * m) ⊕ Fin (n * m)) :
    (fun i => Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v ((Pi.single j 1 : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := F) n m) i)) =
      Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst i; simp
  · simp [Pi.single_eq_of_ne h]

theorem integralFrameAt_eventually : ∀ᶠ v in cofinite, IntegralFrameAt F d n m H K P v := by
  have hr : ∀ᶠ v in cofinite, ∀ j i, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v
      (P.rational.coordinates (Pi.single j 1) i) ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v :=
    Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr fun i => Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F _
  have hi : ∀ᶠ v in cofinite, ∀ j i, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v
      (P.rational.coordinates (Pi.single j (Weil.AdelicSplitting.Integral.Construction.quadraticGenerator d)) i) ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v :=
    Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr fun i => Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F _
  have hb : ∀ᶠ v in cofinite, ∀ i j, Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v
      (P.rational.coordinates.symm (Pi.single i 1) j) ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal_integral F d _
  filter_upwards [hr, hi, hb, Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d] with v hr hi hb hdv
  constructor
  · intro x hx
    apply IntegralFrameCoordinates.linear_coordinates_integral (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v)
      (P.localFrame v).coordinates.toLinearMap
    · intro j i
      have h := P.coordinates_compatible v (Pi.single j 1) i
      rw [rational_tensor_single F d n m, map_one] at h
      exact h.symm ▸ hr j i
    · intro j i
      have h := P.coordinates_compatible v (Pi.single j (Weil.AdelicSplitting.Integral.Construction.quadraticGenerator d)) i
      rw [rational_tensor_single F d n m] at h
      have he : Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v (Weil.AdelicSplitting.Integral.Construction.quadraticGenerator d) =
          Weil.AdelicSplitting.Integral.Construction.quadraticGenerator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) := by
        ext <;> simp [Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal, Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange, Weil.AdelicSplitting.Integral.Construction.quadraticGenerator]
      rw [he] at h
      exact h.symm ▸ hi j i
    · intro j
      exact (QuadraticIntegralCoefficients.quadraticOrder_coefficients F d v hdv (x j)).mp (hx j)
  · intro x hx
    apply IntegralFrameCoordinates.inverse_coordinates_integral (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v)
      (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v) _ (P.localFrame v).coordinates.symm.toLinearMap _ x hx
    · intro a ha
      have hle : (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).map
          (algebraMap (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)) ≤ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v := le_sup_left
      exact hle (Subring.mem_map.mpr ⟨a, ha, rfl⟩)
    · intro i j
      have h := congrFun (Weil.AdelicSplitting.BaseChange.Construction.frame_symm_rational F d n m H K P v (Pi.single i 1)) j
      rw [rational_phase_single F n m] at h
      exact h.symm ▸ hb i j

end

end OAI.RepresentationTheory.Theta.Adelic.GlobalFrameIntegral
