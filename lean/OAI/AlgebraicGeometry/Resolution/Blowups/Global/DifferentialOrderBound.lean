import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialOrderBound
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Differential Order Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialOrderBound.Construction

noncomputable section

/-! Finite intrinsic differential-order bounds on compact smooth integral complex schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

/-- Each affine open has a finite relative differential bound, including
empty opens. Nonempty opens retain the original nonzero ideal. -/
theorem exists_affine_complex_differential_order_bound (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (U : X.affineOpens) : letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
      ∃ n : ℕ, Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (J.ideal U) n = ⊤ := by
  classical
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  by_cases hR : Nontrivial Γ(X, U)
  · let : Nontrivial Γ(X, U) := hR
    let q : PrimeSpectrum Γ(X, U) := Nonempty.some inferInstance
    let : Nonempty U.1 := ⟨U.2.isoSpec.inv q⟩
    let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
    exact Blowups.Smooth.DifferentialOrderBound.Construction.exists_smooth_relative_differential_order_bound ℂ (J.ideal U)
      (Blowup.BlowupRestriction.Construction.nonzero_idealSheaf_on_affineOpen J hJ U)
  · let : Subsingleton Γ(X, U) := not_nontrivial_iff_subsingleton.mp hR
    exact ⟨0, Subsingleton.elim _ _⟩

variable [CompactSpace X]

/-- Compactness supplies one finite differential-order bound for the
original global ideal sheaf on a smooth integral complex scheme. -/
theorem exists_global_complex_differential_order_bound (J : X.IdealSheafData) (hJ : J ≠ ⊥) :
    ∃ n : ℕ, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = ⊤ := by
  classical
  choose b hb using exists_affine_complex_differential_order_bound f J hJ
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := Set.univ)).mp
      ⟨isCompact_univ, isOpen_univ⟩
  let N := hs.toFinset.sup b
  let T := Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J N
  refine ⟨N, (Scheme.IdealSheafData.support_eq_bot_iff T).mp ?_⟩
  apply SetLike.coe_injective
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxcover : x ∈ ⋃ U ∈ s, (U : Set X) := hcover ▸ Set.mem_univ x
  obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp hxcover
  have hNU : b U ≤ N := Finset.le_sup (hs.mem_toFinset.mpr hU)
  have htop : T.ideal U = ⊤ := by
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    have h := Coefficient.UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order ℂ (J.ideal U) hNU
    rw [hb U] at h
    exact top_le_iff.mp h
  have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := T) hxU).mp hx
  rw [htop] at hz
  change x ∈ X.zeroLocus (Set.univ : Set Γ(X, U)) at hz
  rw [Scheme.zeroLocus_univ] at hz
  exact hz hxU

/-- A nonzero proper ideal sheaf has a last proper differential ideal and
a following unit ideal. This selects the intrinsic maximum-order center. -/
theorem exists_global_last_proper_differential_ideal (J : X.IdealSheafData)
    (hJ : J ≠ ⊥) (hproper : J ≠ ⊤) :
    ∃ n : ℕ, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n ≠ ⊤ ∧
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (n + 1) = ⊤ := by
  classical
  have hex := exists_global_complex_differential_order_bound f J hJ
  have hzero : Nat.find hex ≠ 0 := by
    intro he
    have h := Nat.find_spec hex
    rw [he, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_zero] at h
    exact hproper h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  refine ⟨n, Nat.find_min hex (by omega), ?_⟩
  simpa only [hn, Nat.succ_eq_add_one] using Nat.find_spec hex

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialOrderBound.Construction
