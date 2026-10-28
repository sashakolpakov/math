import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.MatrixLargeMinors
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RangeCriterion

/-! # Rank Lower Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankLowerOpen

noncomputable section

/-! Coordinate minors define the open where a matrix has a specified lower rank bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {μ ν : Type u} {X Y : Scheme.{u}}

def matrixRankLowerOpen (A : Matrix ν μ Γ(X, ⊤)) (q : ℕ) : X.Opens :=
  ⨆ (r : ℕ) (_ : q ≤ r) (a : Fin r → μ) (b : Fin r → ν), X.basicOpen (A.submatrix b a).det

theorem matrixRankLowerOpen_mem (A : Matrix ν μ Γ(X, ⊤)) (q : ℕ) (x : X) :
    x ∈ matrixRankLowerOpen A q ↔
      ∃ (r : ℕ), q ≤ r ∧ ∃ (a : Fin r → μ) (b : Fin r → ν),
        x ∈ X.basicOpen (A.submatrix b a).det := by
  simp only [matrixRankLowerOpen, TopologicalSpace.Opens.mem_iSup, exists_prop]

theorem matrixRankLowerOpen_preimage (c : Y ⟶ X) (A : Matrix ν μ Γ(X, ⊤)) (q : ℕ) :
    c ⁻¹ᵁ matrixRankLowerOpen A q = matrixRankLowerOpen (A.map c.appTop.hom) q := by
  simp only [matrixRankLowerOpen, c.preimage_iSup, Scheme.preimage_basicOpen_top]
  congr 1
  funext r
  congr 1
  funext h
  congr 1
  funext a
  congr 1
  funext b
  exact congrArg Y.basicOpen (c.appTop.hom.map_det (A.submatrix b a))

theorem range_subset_basicOpen_iff (c : Y ⟶ X) (r : Γ(X, ⊤)) :
    Set.range c ⊆ (X.basicOpen r : Set X) ↔ IsUnit (c.appTop r) := by
  rw [Open.RangeCriterion.range_subset_open_iff_preimage_eq_top, Scheme.preimage_basicOpen_top,
    Scalar.Nonvanishing.global_isUnit_iff_basicOpen_eq_top]

theorem matrixRankLowerOpen_field_point {K : Type u} [Field K]
    [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
    (c : Spec (.of K) ⟶ X) (A : Matrix ν μ Γ(X, ⊤)) (q : ℕ) :
    (letI : Field Γ(Spec (.of K), ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
        (Field.toIsField K)).toField;
      Set.range c ⊆ (matrixRankLowerOpen A q : Set X) ↔ q ≤ (A.map c.appTop.hom).rank) := by
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  rw [HilbertConstruction.Field.MatrixLargeMinors.field_matrix_rank_le_iff_large_minor]
  constructor
  · intro h
    let t : Spec (.of K) := (⊥ : PrimeSpectrum K)
    obtain ⟨r, hqr, a, b, ht⟩ := (matrixRankLowerOpen_mem A q (c t)).mp (h ⟨t, rfl⟩)
    have hr : Set.range c ⊆ (X.basicOpen (A.submatrix b a).det : Set X) := by
      rintro z ⟨s, rfl⟩
      exact (Subsingleton.elim s t) ▸ ht
    have hu := (range_subset_basicOpen_iff c (A.submatrix b a).det).mp hr
    refine ⟨r, hqr, a, b, ?_⟩
    exact (c.appTop.hom.map_det (A.submatrix b a)) ▸ hu.ne_zero
  · rintro ⟨r, hqr, a, b, hdet⟩ z hz
    have hu : IsUnit (c.appTop (A.submatrix b a).det) := by
      rw [c.appTop.hom.map_det (A.submatrix b a)]
      exact isUnit_iff_ne_zero.mpr hdet
    exact (matrixRankLowerOpen_mem A q z).mpr
      ⟨r, hqr, a, b, (range_subset_basicOpen_iff c _).mpr hu hz⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankLowerOpen
