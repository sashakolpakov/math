import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeDifferentialGenerators
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativePartialBaseChange

/-! # Differential Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBaseChange.Construction

noncomputable section

/-! Exact étale base change for relative differential ideals on polynomial charts. -/

variable {σ K S T ι : Type*} [Field K] [CommRing S] [CommRing T] [Fintype σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]
  [Algebra S T] [Algebra.FormallyEtale S T]
  [Algebra (MvPolynomial σ K) T] [Algebra.Etale (MvPolynomial σ K) T]
  [Algebra K T] [IsScalarTower K S T] [IsScalarTower K (MvPolynomial σ K) T]
  [IsScalarTower (MvPolynomial σ K) S T]

include σ in
theorem etale_firstRelativeDifferentialIdeal_span_baseChange (p : ι → S) :
    (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal K (Ideal.span (Set.range p))).map (algebraMap S T) =
      DifferentialBlowup.Construction.firstRelativeDifferentialIdeal K (Ideal.span (Set.range (fun i => algebraMap S T (p i)))) := by
  have h0 : (Ideal.span (Set.range p)).map (algebraMap S T) =
      Ideal.span (Set.range (fun i => algebraMap S T (p i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have h1 : (Ideal.span (Set.range
      (fun t : σ × ι => Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) t.1 (p t.2)))).map (algebraMap S T) =
      Ideal.span (Set.range (fun t : σ × ι =>
        Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := T) t.1 (algebraMap S T (p t.2)))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext t
    exact (Blowups.Etale.RelativePartialBaseChange.Construction.etaleRelativePartial_baseChange t.1 (p t.2)).symm
  rw [Blowups.Etale.RelativeDifferentialGenerators.Construction.etale_firstRelativeDifferentialIdeal_span (σ := σ) p, Ideal.map_sup, h0, h1,
    Blowups.Etale.RelativeDifferentialGenerators.Construction.etale_firstRelativeDifferentialIdeal_span (σ := σ) (S := T)]

include σ in
/-- Formation of the first intrinsic relative differential ideal
commutes exactly with the étale refinement, for every original ideal. -/
theorem etale_firstRelativeDifferentialIdeal_baseChange (J : Ideal S) :
    (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal K J).map (algebraMap S T) =
      DifferentialBlowup.Construction.firstRelativeDifferentialIdeal K (J.map (algebraMap S T)) := by
  let p : J → S := Subtype.val
  have hspan : Ideal.span (Set.range p) = J := by
    rw [Subtype.range_val, Ideal.span_eq]
  have hmap : Ideal.span (Set.range (fun i => algebraMap S T (p i))) = J.map (algebraMap S T) := by
    calc
      Ideal.span (Set.range (fun i => algebraMap S T (p i))) =
          (Ideal.span (Set.range p)).map (algebraMap S T) := by
        rw [Ideal.map_span, ← Set.range_comp]
        rfl
      _ = J.map (algebraMap S T) := congrArg (Ideal.map (algebraMap S T)) hspan
  have h := etale_firstRelativeDifferentialIdeal_span_baseChange (σ := σ) (K := K) (T := T) p
  rw [hspan, hmap] at h
  exact h

include σ in
/-- All iterated relative differential ideals therefore agree on
étale refinements and, in particular, overlapping principal affine opens. -/
theorem etale_iteratedRelativeDifferentialIdeal_baseChange (J : Ideal S) (n : ℕ) :
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K J n).map (algebraMap S T) =
      DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K (J.map (algebraMap S T)) n := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    change (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal K J) n).map
      (algebraMap S T) = DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal K
        (J.map (algebraMap S T))) n
    rw [ih, etale_firstRelativeDifferentialIdeal_baseChange (σ := σ)]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBaseChange.Construction
