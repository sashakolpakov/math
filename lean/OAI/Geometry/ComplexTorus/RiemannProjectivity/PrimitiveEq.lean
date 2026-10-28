import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace
import Mathlib.Analysis.Calculus.MeanValue

/-! # Primitive Eq -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.PrimitiveEq.Constructions.Primitive

noncomputable section

/-!
# RiemannProjectivity: separating a primitive into its periods and a periodic function

A primitive on the vector-space cover of a torus has a lattice-periodic
derivative. Its lattice increments form an additive character. Extending that
character along a lattice basis gives a real-linear covector; subtracting the
covector leaves a lattice-periodic primitive. These are the descent steps for
the first de Rham cohomology comparison, proved without a comparison axiom.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A periodic derivative makes every lattice increment independent of
the starting point. -/
theorem increment_eq (F : V → ℂ) (hF : Differentiable ℝ F)
    (t : V) (hperiod : ∀ z, fderiv ℝ F (z + t) = fderiv ℝ F z) (z : V) :
    F (z + t) - F z = F t - F 0 := by
  have hd : ∀ y, HasFDerivAt (𝕜 := ℝ) (fun w => F (w + t) - F w) 0 y := by
    intro y
    convert! ((hF (y + t)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).add_const t)).sub (hF y).hasFDerivAt using 1
    simp [hperiod y]
  have hconst := is_const_of_fderiv_eq_zero
    (fun y => (hd y).differentiableAt) (fun y => (hd y).fderiv) z 0
  simpa using hconst

variable (Λ : Submodule ℤ V) (F : V → ℂ) (hF : Differentiable ℝ F)
  (hperiod : ∀ z t, t ∈ Λ → fderiv ℝ F (z + t) = fderiv ℝ F z)

/-- The increment of a primitive is an actual additive character of the lattice. -/
def latticeCharacter : Λ →+ ℂ where
  toFun t := F t - F 0
  map_zero' := by simp
  map_add' s t := by
    have h := increment_eq F hF t (fun z => hperiod z t t.property) s
    change F ((s : V) + (t : V)) - F (s : V) = F (t : V) - F 0 at h
    change F ((s : V) + (t : V)) - F 0 = (F (s : V) - F 0) + (F (t : V) - F 0)
    linear_combination h

theorem latticeCharacter_increment (z : V) (t : Λ) :
    F (z + t) - F z = latticeCharacter Λ F hF hperiod t :=
  increment_eq F hF t (fun z => hperiod z t t.property) z

variable [FiniteDimensional ℝ V] [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- Every lattice character extends uniquely to a continuous real-linear
covector on its ambient real vector space. -/
theorem exists_covector_extending_character (χ : Λ →+ ℂ) :
    ∃! l : V →L[ℝ] ℂ, ∀ t : Λ, l t = χ t := by
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := b.ofZLatticeBasis ℝ Λ
  let l : V →L[ℝ] ℂ := (bR.constr ℝ (fun i => χ (b i))).toContinuousLinearMap
  have hl : (l.toLinearMap.restrictScalars ℤ).comp Λ.subtype = χ.toIntLinearMap := by
    apply b.ext
    intro i
    change l (b i : V) = χ (b i)
    rw [← b.ofZLatticeBasis_apply ℝ Λ i]
    exact bR.constr_basis ℝ (fun i => χ (b i)) i
  refine ⟨l, fun t => LinearMap.congr_fun hl t, ?_⟩
  intro m hm
  apply ContinuousLinearMap.coe_injective
  apply bR.ext
  intro i
  change m (bR i) = l (bR i)
  rw [b.ofZLatticeBasis_apply ℝ Λ, hm]
  exact (LinearMap.congr_fun hl (b i)).symm

include hF hperiod in
/-- Subtracting the unique real-linear period covector leaves a function
that descends through the lattice quotient. -/
theorem exists_periodic_remainder :
    ∃ l : V →L[ℝ] ℂ,
      (∀ z t, t ∈ Λ → F (z + t) - F z = l t) ∧
      ∀ z t, t ∈ Λ → F (z + t) - l (z + t) = F z - l z := by
  obtain ⟨l, hl, _⟩ := exists_covector_extending_character Λ (latticeCharacter Λ F hF hperiod)
  have hinc (z t : V) (ht : t ∈ Λ) : F (z + t) - F z = l t := by
    rw [hl ⟨t, ht⟩]
    exact latticeCharacter_increment Λ F hF hperiod z ⟨t, ht⟩
  refine ⟨l, hinc, ?_⟩
  intro z t ht
  rw [map_add]
  linear_combination hinc z t ht

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.PrimitiveEq.Constructions.Primitive
