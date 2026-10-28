import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedIdealContainment
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalHypersurfaceStep

/-! # Intrinsic Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicStep.Construction

noncomputable section

/-! A complete intrinsic order-reduction step on any smooth affine curve. -/

open _root_.CategoryTheory

universe u

section Basic

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

theorem first_iteratedRelativeDifferentialIdeal (J : Ideal R) (n : ℕ) :
    Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih => exact ih (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J)

end Basic

variable (k : Type u) {R : Type u} [CommRing R]
  [Field k] [IsAlgClosed k] [Algebra k R] [Algebra ℚ R] [IsNoetherianRing R] [Algebra.Smooth k R]

/-- In dimension at most one, the original intrinsic tangent ideal is a
permissible center. Containment descends from the derivative neighborhoods. -/
theorem curve_tangent_center_permissible (hd : ringKrullDim R ≤ 1) (J : Ideal R) (n : ℕ)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤) :
    J ≤ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) ^ (n + 1) := by
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  have hT : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k T = ⊤ :=
    (first_iteratedRelativeDifferentialIdeal k J n).trans hbound
  let s : Set R := (T : Set R) ∪ Set.range (fun t : Derivation k R R × T => t.1 t.2.val)
  have hs : Ideal.span s = ⊤ := by
    rw [Ideal.span_union, Ideal.span_eq]
    exact hT
  apply LocalizedIdealContainment.Construction.ideal_le_of_localized_away_cover J (T ^ (n + 1)) s hs
  rintro r (hr | ⟨⟨D, z⟩, rfl⟩)
  · rw [Ideal.map_pow, IdempotentQuotientCenter.Construction.center_map_away_member_eq_top T r hr, Ideal.top_pow]
    exact le_top
  · let A := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z.val
    let H := DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood D z.val
    let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway (D z.val)
    let : Algebra.Smooth k H := DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood_smooth D z.val
    let : IsReduced H := Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k
    have hdH : ringKrullDim H ≤ 0 :=
      HypersurfaceDimension.Construction.differentialHypersurfaceNeighborhood_dimension_induction D z.val 0 (by simpa using hd)
    have hmap : T.map (algebraMap R A) =
        Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R A)) n :=
      Blowups.Smooth.DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange k J n
    have hz : algebraMap R A z.val ∈
        Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R A)) n := by
      rw [← hmap]
      exact Ideal.mem_map_of_mem _ z.property
    have hperm := (ZeroDimensionalHypersurfaceCenter.Construction.zero_dimensional_hypersurface_intrinsic_center k
      (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation D z.val) (algebraMap R A z.val)
      (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation_equation D z.val) hdH
      (J.map (algebraMap R A)) n hz).1
    rw [Ideal.map_pow, hmap]
    exact hperm

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- A smooth affine curve has a single canonical order-reduction step:
the intrinsic tangent ideal is a permissible smooth center, its actual blowup
is an isomorphism, and every actual denominator chart has lower order. -/
theorem curve_intrinsic_tangent_step (hd : ringKrullDim R ≤ 1) (J : Ideal R) (n : ℕ)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤) :
    let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
    J ≤ T ^ (n + 1) ∧ Algebra.Smooth k (R ⧸ T) ∧ IsIso (ReesGrading.Construction.affineBlowupToSpec T) ∧
      ∀ a : T, Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform T J (n + 1) a) n = ⊤ := by
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  have hT : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k T = ⊤ :=
    (first_iteratedRelativeDifferentialIdeal k J n).trans hbound
  have hperm := curve_tangent_center_permissible k hd J n hbound
  refine ⟨hperm, DifferentialCenter.Construction.curve_center_smooth_of_first_differential_top k hd T hT,
    CenterBlowup.Construction.curve_center_blowup_isIso_of_first_differential_top k hd T hT, ?_⟩
  intro a
  exact Coefficient.UnitBlowup.Construction.relative_hypersurface_denominator_differential_unit k T J a n hperm a.property

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicStep.Construction
