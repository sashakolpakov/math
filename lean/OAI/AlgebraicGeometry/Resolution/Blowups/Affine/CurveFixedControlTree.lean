import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFixedControlStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveChart
import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianCoordinateTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion

/-! # Curve Fixed Control Tree -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFixedControlTree.Construction

noncomputable section

/-! Finite trees of actual affine curve blowup charts at a fixed positive control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Every node records an actual smooth permissible center and a finite
generating family covering its actual blowup. Children use the original
coefficient algebra and the same control. Terminal ideals have empty order locus. -/
inductive AffineCurveFixedControlTree (k : Type u) [CommRing k] (b : ℕ) :
    (R : CommRingCat.{u}) → [Algebra k R] → Ideal R → Type (u + 1)
  | terminal {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (hterminal : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (b - 1) = ⊤) :
      AffineCurveFixedControlTree k b R J
  | blowup {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
      (I : Ideal R) (hb : 0 < b) (hperm : J ≤ I ^ b)
      (hsmooth : Algebra.Smooth k (R ⧸ I)) (hπ : IsIso (ReesGrading.Construction.affineBlowupToSpec I))
      (s : Finset I) (hgen : Ideal.span (Set.range (fun x : s => (x.val : I).val)) = I)
      (children : ∀ a : s, AffineCurveFixedControlTree k b (.of (Blowup.Charts.Construction.blowupChart I a.val))
        (ControlledTransform.Construction.blowupControlledTransform I J b a.val)) :
      AffineCurveFixedControlTree k b R J

def AffineCurveFixedControlTree.height {k : Type u} [CommRing k] {b : ℕ}
    {R : CommRingCat.{u}} [Algebra k R] {J : Ideal R}
    (T : Construction.AffineCurveFixedControlTree k b R J) : ℕ := by
  classical
  induction T with
  | terminal ht => exact 0
  | blowup I hb hperm hsmooth hπ s hgen children ih => exact (Finset.univ.sup ih) + 1

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- A finite differential bound constructs a finitely branching tree of
actual curve blowups. The bound strictly decreases on every nonterminal branch,
and the prescribed positive control remains unchanged. -/
theorem exists_bounded_affine_curve_fixed_control_tree (b : ℕ) (hb : 0 < b) (n : ℕ) :
    ∀ (R : CommRingCat.{u}) [Algebra k R] [Algebra ℚ R] [IsNoetherianRing R]
      [Algebra.Smooth k R] (J : Ideal R), ringKrullDim R ≤ 1 →
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤ →
      ∃ T : Construction.AffineCurveFixedControlTree k b R J, T.height ≤ n := by
  classical
  induction n with
  | zero =>
      intro R _ _ _ _ J _ hbound
      have h := Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J (Nat.zero_le (b - 1))
      rw [hbound] at h
      exact ⟨.terminal (top_le_iff.mp h), Nat.zero_le _⟩
  | succ n ih =>
      intro R _ _ _ _ J hd hbound
      by_cases hbn : b ≤ n + 1
      · let I := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
        obtain ⟨hperm, hsmooth, hπ, hnext⟩ := CurveFixedControlStep.Construction.affine_curve_fixed_control_step k hd J n b hb hbn hbound
        let : IsIso (ReesGrading.Construction.affineBlowupToSpec I) := hπ
        obtain ⟨s, hgen⟩ := CurveChart.Construction.exists_finite_blowup_generators I
        have hchildren (a : s) : ∃ T : Construction.AffineCurveFixedControlTree k b
            (.of (Blowup.Charts.Construction.blowupChart I a.val)) (ControlledTransform.Construction.blowupControlledTransform I J b a.val), T.height ≤ n := by
          let : IsNoetherianRing (Blowup.Charts.Construction.blowupChart I a.val) := NoetherianCoordinateTransform.Construction.blowupChart_isNoetherian I a.val
          let : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I a.val) := CurveChart.Construction.blowupChart_smooth_of_isIso k I a.val
          exact ih (.of (Blowup.Charts.Construction.blowupChart I a.val)) (ControlledTransform.Construction.blowupControlledTransform I J b a.val)
            ((OpenDimension.Construction.blowupChart_ringKrullDim_le_of_isIso I a.val).trans hd) (hnext a.val)
        refine ⟨.blowup I hb hperm hsmooth hπ s hgen (fun a => (hchildren a).choose), ?_⟩
        change (Finset.univ.sup fun a => (hchildren a).choose.height) + 1 ≤ n + 1
        exact Nat.add_le_add_right (Finset.sup_le (fun a _ => (hchildren a).choose_spec)) 1
      · have h := Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k J
          (show n + 1 ≤ b - 1 by omega)
        rw [hbound] at h
        exact ⟨.terminal (top_le_iff.mp h), Nat.zero_le _⟩

/-- A finite tree exists at each positive control for every smooth affine
curve ideal with a finite differential bound. -/
theorem exists_affine_curve_fixed_control_tree (b : ℕ) (hb : 0 < b) (n : ℕ)
    (R : CommRingCat.{u}) [Algebra k R] [Algebra ℚ R] [IsNoetherianRing R]
    [Algebra.Smooth k R] (J : Ideal R) (hd : ringKrullDim R ≤ 1)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤) :
    Nonempty (Construction.AffineCurveFixedControlTree k b R J) := by
  obtain ⟨T, _⟩ := exists_bounded_affine_curve_fixed_control_tree k b hb n R J hd hbound
  exact ⟨T⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.CurveFixedControlTree.Construction
