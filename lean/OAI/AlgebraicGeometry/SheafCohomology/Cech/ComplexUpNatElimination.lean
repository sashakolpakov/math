import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCycles
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Complex Up Nat Elimination -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatElimination.Projective

noncomputable section

/-! Eliminating a bidegree coordinate by an actual total boundary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u

private theorem hom_map_units_smul {A B : AddCommGrpCat.{u}}
    (f : A ⟶ B) (r : ℤˣ) (x : A) : f (r • x) = r • f x := by
  change f.hom ((r : ℤ) • x) = (r : ℤ) • f.hom x
  exact f.hom.map_zsmul _ _

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- The boundary of an element in one bidegree has the expected signed row component. -/
theorem total_boundary_same_row (q p : ℕ) (y : (K.X q).X p) :
    (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl y)) =
      ((-1 : ℤˣ) ^ q) • (K.X q).d p (p + 1) y := by
  have h := congrArg (fun f => f y)
    (UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat_assoc K q p ((UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1)))
  simpa [ConcreteCategory.comp_apply, Units.smul_def] using h

/-- Such a boundary has no component in any preceding row. -/
theorem total_boundary_before_row (q p a b : ℕ) (ha : a < q) (y : (K.X q).X p) :
    (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl y)) = 0 := by
  have hq : q ≠ a := by omega
  have hq' : q + 1 ≠ a := by omega
  have h := congrArg (fun f => f y)
    (UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat_assoc K q p ((UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)))
  simpa [ConcreteCategory.comp_apply, hq, hq'] using h

/-- Row exactness lets one remove a row-cycle coordinate by subtracting a total boundary,
while preserving every preceding row coordinate. -/
theorem exists_remove_row_coordinate (q p : ℕ)
    (x : (K.total (.up ℕ)).X (q + p + 1))
    (hrow : (ShortComplex.mk ((K.X q).d p (p + 1))
      ((K.X q).d (p + 1) (p + 2)) ((K.X q).d_comp_d p (p + 1) (p + 2))).Exact)
    (hcycle : (K.X q).d (p + 1) (p + 2)
      ((UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1) x) = 0) :
    ∃ z : (K.total (.up ℕ)).X (q + p),
      (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1)
        (x - (K.total (.up ℕ)).d (q + p) (q + p + 1) z) = 0 ∧
      ∀ a b, a < q →
        (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)
          (x - (K.total (.up ℕ)).d (q + p) (q + p + 1) z) =
            (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1) x := by
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp hrow _ hcycle
  let r : ℤˣ := (-1) ^ q
  let z := K.ιTotal (.up ℕ) q p (q + p) rfl (r⁻¹ • y)
  refine ⟨z, ?_, ?_⟩
  · have hz : (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1)
        ((K.total (.up ℕ)).d (q + p) (q + p + 1) z) =
          (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1) x := by
      dsimp only [z]
      rw [total_boundary_same_row, hom_map_units_smul]
      change r • (r⁻¹ • (K.X q).d p (p + 1) y) = _
      rw [smul_inv_smul]
      exact hy
    rw [map_sub, hz, sub_self]
  · intro a b ha
    rw [map_sub]
    change _ - (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl (r⁻¹ • y))) = _
    rw [total_boundary_before_row K q p a b ha, sub_zero]

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatElimination.Projective
