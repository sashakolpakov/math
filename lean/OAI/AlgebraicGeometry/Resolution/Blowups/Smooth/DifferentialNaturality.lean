import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveDualIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import Mathlib.RingTheory.Smooth.Basic

/-! # Differential Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality.Construction

noncomputable section

/-! Differential ideals on smooth algebras commute with étale maps without chosen coordinates. -/

variable (k : Type*) {R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra.Smooth k R]

/-- A derivation after scalar extension takes an original ideal section
into the extension of its intrinsic first differential ideal. -/
theorem smooth_derivation_base_section_mem (J : Ideal R) (D : Derivation k S S)
    (x : R) (hx : x ∈ J) :
    D (algebraMap R S x) ∈ (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J).map (algebraMap R S) := by
  let E := D.compAlgebraMap R
  have h := ProjectiveDualIdeal.Construction.projective_linearMap_mem_ideal_map (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J)
    (KaehlerDifferential.D k R x) (fun l =>
      Relative.DifferentialBlowup.Construction.relative_derivation_mem_first k J (l.compDer (KaehlerDifferential.D k R)) hx)
    E.liftKaehlerDifferential
  rw [Derivation.liftKaehlerDifferential_comp_D] at h
  exact h

/-- The first differential ideal after scalar extension is contained in
the extension of the original one for every map from a smooth algebra. -/
theorem smooth_firstRelativeDifferentialIdeal_baseChange_le (J : Ideal R) :
    Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J.map (algebraMap R S)) ≤
      (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J).map (algebraMap R S) := by
  let L := (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J).map (algebraMap R S)
  have hJ : J.map (algebraMap R S) ≤ L := Ideal.map_mono (Relative.DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k J)
  apply sup_le hJ
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨D, x⟩, rfl⟩
  let p : J → S := fun y => algebraMap R S y.val
  have hspan : Ideal.span (Set.range p) = J.map (algebraMap R S) := by
    have hs : Ideal.span (Set.range (Subtype.val : J → R)) = J := by
      rw [Subtype.range_val, Ideal.span_eq]
    have hm := congrArg (Ideal.map (algebraMap R S)) hs
    rw [Ideal.map_span, ← Set.range_comp] at hm
    exact hm
  have hx : x.val ∈ Ideal.span (Set.range p) := hspan.symm ▸ x.property
  have hD := Relative.DifferentialBlowup.Construction.relative_derivation_of_span k D p hx
  apply (sup_le (hspan.le.trans hJ) ?_) hD
  apply Ideal.span_le.mpr
  rintro _ ⟨y, rfl⟩
  exact smooth_derivation_base_section_mem k J D y.val y.property

variable [Algebra.FormallyEtale R S]

/-- Exact étale compatibility of the intrinsic first differential ideal on
any smooth affine algebra, with no global coordinate frame. -/
theorem smooth_firstRelativeDifferentialIdeal_baseChange (J : Ideal R) :
    (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J).map (algebraMap R S) =
      Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J.map (algebraMap R S)) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply sup_le
    · intro x hx
      exact Relative.DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k _ (Ideal.mem_map_of_mem _ hx)
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨D, x⟩, rfl⟩
      change algebraMap R S (D x.val) ∈ Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J.map (algebraMap R S))
      rw [← Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (S := S) D x.val]
      exact Relative.DifferentialBlowup.Construction.relative_derivation_mem_first k _ (Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D)
        (Ideal.mem_map_of_mem _ x.property)
  · exact smooth_firstRelativeDifferentialIdeal_baseChange_le k J

/-- The full intrinsic differential filtration agrees under étale maps of
smooth affine algebras and hence under every principal affine restriction. -/
theorem smooth_iteratedRelativeDifferentialIdeal_baseChange (J : Ideal R) (n : ℕ) :
    (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (algebraMap R S) =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R S)) n := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J) n).map
      (algebraMap R S) = Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
        (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J.map (algebraMap R S))) n
    rw [ih, smooth_firstRelativeDifferentialIdeal_baseChange k J]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality.Construction
