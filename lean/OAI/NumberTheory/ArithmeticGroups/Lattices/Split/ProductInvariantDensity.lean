import OAI.NumberTheory.ArithmeticGroups.Lattices.WeightedMeasureCovariance
import OAI.NumberTheory.ArithmeticGroups.Lattices.RightInvariantMeasureCoordinates
import Mathlib.Tactic.Group

/-! # Product Invariant Density -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ProductInvariantDensity.Construction

noncomputable section

/-! The scaling character of the unipotent conjugation action gives
the right-invariant exponential density in split/unipotent product coordinates. -/

open scoped ENNReal
open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem split_product_weighted_measure_right_invariant
    {A N G : Type*} [Group A] [Group N] [Group G]
    [MeasurableSpace A] [MeasurableSpace N] [MeasurableSpace G]
    [MeasurableMul A] [MeasurableMul N] [MeasurableMul G]
    (α : A →* G) (β : N →* G) (e : A × N ≃ᵐ G)
    (he : ∀ x : A × N, e x = α x.1 * β x.2)
    (γ : A → N → N) (hγm : ∀ a, Measurable (γ a))
    (hγ : ∀ a n, β (γ a n) = (α a)⁻¹ * β n * α a)
    (χ : A →* ℝ≥0∞) (hχ : Measurable χ)
    (μ : Measure A) (ν : Measure N) [SFinite μ] [SFinite ν]
    [IsMulRightInvariant μ] [IsMulRightInvariant ν]
    (hscale : ∀ a, ν.map (γ a) = χ a • ν) :
    IsMulRightInvariant (((μ.withDensity χ).prod ν).map e) := by
  let ρ := μ.withDensity χ
  let τ : G → A × N → A × N := fun g x =>
    (x.1 * (e.symm g).1, γ (e.symm g).1 x.2 * (e.symm g).2)
  have hτ (g : G) : MeasurePreserving (τ g) (ρ.prod ν) (ρ.prod ν) := by
    let a := (e.symm g).1
    let n := (e.symm g).2
    have hμ : χ a • ρ.map (· * a) = ρ :=
      WeightedMeasureCovariance.Construction.withDensity_map_covariance μ (· * a) (measurePreserving_mul_right μ a) χ hχ (χ a)
        (fun x => by rw [map_mul, mul_comm])
    have hp := WeightedMeasureCovariance.Construction.measurePreserving_product_of_opposite_scalings ρ ν (· * a) (γ a)
      (measurable_mul_const a) (hγm a) (χ a) hμ (hscale a)
    exact ((MeasurePreserving.id ρ).prod (measurePreserving_mul_right ν n)).comp hp
  apply RightInvariantMeasureCoordinates.Construction.isMulRightInvariant_map_of_coordinates e (ρ.prod ν) τ hτ
  intro g x
  have hg : g = α (e.symm g).1 * β (e.symm g).2 :=
    (e.apply_symm_apply g).symm.trans (he (e.symm g))
  rw [he, he]
  change α (x.1 * (e.symm g).1) * β (γ (e.symm g).1 x.2 * (e.symm g).2) =
    (α x.1 * β x.2) * g
  rw [map_mul, map_mul, hγ]
  conv_rhs => rw [hg]
  group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ProductInvariantDensity.Construction
