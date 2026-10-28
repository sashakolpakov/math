import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.DolbeaultPoincare
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

/-! # Local Dolbeault Poincare -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LocalDolbeaultPoincare

noncomputable section

/-! The actual local Dolbeault lemma in every positive antiholomorphic
degree on every finite-dimensional complex normed chart model. -/

open _root_.TopologicalSpace Set

open OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem localDolbeaultPoincare_higher (O : Opens E) (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm O (n + 2)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (x : O) :
    ∃ V : Opens E, x.val ∈ V ∧ ∃ hV : V ≤ O,
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V (n + 1), DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧
        DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hV a := by
  let d := Module.finrank ℂ E
  let e : (Fin d → ℂ) ≃L[ℂ] E := (Module.finBasis ℂ E).equivFun.symm.toContinuousLinearEquiv
  let U : Opens (Fin d → ℂ) := ⟨e ⁻¹' (O : Set E), O.isOpen.preimage e.continuous⟩
  have hmap : MapsTo e (U : Set (Fin d → ℂ)) (O : Set E) := fun _ hy => hy
  let A := DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback e.toContinuousLinearMap hmap a
  have hA : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) A = 0 := DivisorClass.Chern.CoordinatePullbackIdentities.complexLinearOpenPullback_closed e.toContinuousLinearMap hmap a ha
  have hAp : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) A :=
    DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree e.toContinuousLinearMap hmap hpure
  let y : U := ⟨e.symm x, by
    change e (e.symm x) ∈ O
    simpa only [e.apply_symm_apply] using x.property⟩
  obtain ⟨W, hyW, hW, t, htp, ht⟩ := Coordinate.DolbeaultPoincare.coordinateDolbeaultPoincare_higher U n p q hn A hA hAp y
  let V : Opens E := ⟨e '' (W : Set (Fin d → ℂ)), e.toHomeomorph.isOpenMap _ W.isOpen⟩
  have hVO : V ≤ O := by
    rintro z ⟨u, hu, rfl⟩
    exact hW hu
  have hInv : MapsTo e.symm (V : Set E) (W : Set (Fin d → ℂ)) := by
    rintro z ⟨u, hu, rfl⟩
    simpa only [e.symm_apply_apply] using hu
  let t' := DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback e.symm.toContinuousLinearMap hInv t
  refine ⟨V, ⟨e.symm x, hyW, e.apply_symm_apply x⟩, hVO, t',
    DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree e.symm.toContinuousLinearMap hInv htp, ?_⟩
  have hd := DivisorClass.Chern.Complex.LinearOpenPullback.openDolbeaultD_complexLinearPullback e.symm.toContinuousLinearMap hInv t
  have htransport := congrArg (DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback e.symm.toContinuousLinearMap hInv) ht
  have hroundtrip := DivisorClass.Chern.CoordinatePullbackIdentities.complexLinearOpenPullback_inverse_restrict e.symm hmap hInv hVO hW a
  exact hd.trans (htransport.trans hroundtrip)

theorem localDolbeaultPoincare (O : Opens E) (n p q : ℕ) (hn : n = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm O (n + 1)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (x : O) :
    ∃ V : Opens E, x.val ∈ V ∧ ∃ hV : V ≤ O,
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n, DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧
        DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hV a := by
  cases n with
  | zero =>
      have hp : p = 0 := by omega
      have hq : q = 0 := by omega
      subst p q
      obtain ⟨V, hxV, hV, t, ht⟩ := DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.localDolbeaultPoincare_one O a ha hpure x
      exact ⟨V, hxV, hV, t, fun y => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E (t y), ht⟩
  | succ n =>
      exact localDolbeaultPoincare_higher O n p q hn a ha hpure x

end

end OAI.AlgebraicGeometry.Comparison.Betti.LocalDolbeaultPoincare
