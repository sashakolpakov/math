import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Total Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalCoordinates

noncomputable section

/-! Module coordinates and row elimination for the actual first-quadrant total complex. -/

open _root_.CategoryTheory Limits Preadditive

universe u v

variable {R : Type u} [CommRing R]

private def homEvaluation {A B : ModuleCat.{v} R} (x : A) : (A ⟶ B) →+ B where
  toFun f := f x
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem hom_sum_apply {A B : ModuleCat.{v} R} {ι : Type*}
    (s : Finset ι) (f : ι → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  map_sum (homEvaluation x) f s

variable (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  [K.HasTotal (.up ℕ)]

def ZeroRowsBefore (n : ℕ) (x : (K.total (.up ℕ)).X n) (q : ℕ) : Prop :=
  ∀ a b, a + b = n → a < q → (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b n x = 0

theorem eq_zero_of_coordinates (n : ℕ) (x : (K.total (.up ℕ)).X n)
    (h : ∀ i : Fin (n + 1), (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) i (n - i) n x = 0) : x = 0 := by
  have he := congrArg (fun f => f x) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCoordinates.Projective.totalUpNat_decomposition K n)
  rw [hom_sum_apply] at he
  simpa only [ConcreteCategory.comp_apply, h, map_zero, Finset.sum_const_zero,
    CategoryTheory.id_apply] using he.symm

theorem cycle_row (n q p : ℕ) (hdeg : q + p = n)
    (x : (K.total (.up ℕ)).X n)
    (hx : (K.total (.up ℕ)).d n (n + 1) x = 0)
    (hbefore : ZeroRowsBefore K n x q) :
    (K.X q).d p (p + 1) ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q p n x) = 0 := by
  cases q with
  | zero =>
      have hn : p = n := by omega
      clear hdeg
      subst n
      have h := congrArg (fun f => f x) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero K p)
      simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h.symm
  | succ q =>
      have hn : q + p + 1 = n := by omega
      clear hdeg
      subst n
      have h := congrArg (fun f => f x) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_interior K q p)
      have hp := hbefore q (p + 1) (by omega) (by omega)
      have hz : ((-1 : ℤˣ) ^ (q + 1)) •
          (K.X (q + 1)).d p (p + 1)
            ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) (q + 1) p (q + p + 1) x) = 0 := by
        simpa [ConcreteCategory.comp_apply, hx, hp, Units.smul_def] using h.symm
      exact (smul_eq_zero_iff_eq _).mp hz

theorem boundary_same_row (q p : ℕ) (y : (K.X q).X p) :
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl y)) =
      ((-1 : ℤˣ) ^ q) • (K.X q).d p (p + 1) y := by
  have h := congrArg (fun f => f y)
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat_assoc K q p ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1)))
  simpa [ConcreteCategory.comp_apply, Units.smul_def] using h

theorem boundary_before_row (q p a b : ℕ) (ha : a < q) (y : (K.X q).X p) :
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl y)) = 0 := by
  have hq : q ≠ a := by omega
  have hq' : q + 1 ≠ a := by omega
  have h := congrArg (fun f => f y)
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat_assoc K q p ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)))
  simpa [ConcreteCategory.comp_apply, hq, hq'] using h

theorem remove_boundary_coordinate (q p : ℕ)
    (x : (K.total (.up ℕ)).X (q + p + 1))
    (y : (K.X q).X p)
    (hy : (K.X q).d p (p + 1) y = (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1) x)
    (hbefore : ZeroRowsBefore K (q + p + 1) x q) :
    ∃ z : (K.total (.up ℕ)).X (q + p),
      ZeroRowsBefore K (q + p + 1)
        (x - (K.total (.up ℕ)).d (q + p) (q + p + 1) z) (q + 1) := by
  let r : ℤˣ := (-1) ^ q
  let z := K.ιTotal (.up ℕ) q p (q + p) rfl (r⁻¹ • y)
  have hz : (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1) z) =
        (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1) x := by
    dsimp only [z]
    rw [boundary_same_row]
    have hsmul : (K.X q).d p (p + 1) (r⁻¹ • y) =
        r⁻¹ • (K.X q).d p (p + 1) y := by
      change (K.X q).d p (p + 1) ((r⁻¹ : ℤˣ).val • y) = _
      exact (K.X q).d p (p + 1) |>.hom.toAddMonoidHom.map_zsmul (r⁻¹ : ℤˣ).val y
    rw [hsmul]
    change r • (r⁻¹ • (K.X q).d p (p + 1) y) = _
    rw [smul_inv_smul, hy]
  refine ⟨z, ?_⟩
  intro a b hab ha
  by_cases haq : a < q
  · rw [map_sub]
    change _ - (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl (r⁻¹ • y))) = 0
    rw [boundary_before_row K q p a b haq, sub_zero]
    exact hbefore a b hab haq
  · have heqa : a = q := by omega
    have heqb : b = p + 1 := by omega
    subst a b
    rw [map_sub, hz, sub_self]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalCoordinates
