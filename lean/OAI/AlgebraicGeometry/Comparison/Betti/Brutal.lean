import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD
import Mathlib.Algebra.Homology.QuasiIso

/-! # Brutal -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Brutal.Complex

noncomputable section

/-! Exact component behavior of the original brutal truncation,
including comparison above the cutoff after a functor preserving zero morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

open _root_.Complex

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]

theorem brutal_inclusionTerm_isIso (K : CochainComplex C ℕ) (r : ℤ) (n : ℕ) (hr : r ≤ (n : ℤ)) :
    IsIso (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n) := by
  simp only [Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left hr]
  infer_instance

theorem brutal_isZero_X_below (K : CochainComplex C ℕ) (r : ℤ) (n : ℕ) (hr : (n : ℤ) < r) :
    IsZero ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).X n) := by
  change IsZero (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n)
  rw [Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_right (not_le.mpr hr)]
  exact isZero_zero C

theorem brutal_inclusion_isIso_of_nonpos (K : CochainComplex C ℕ) (r : ℤ) (hr : r ≤ 0) :
    IsIso (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) := by
  have h (n : ℕ) : IsIso ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r).f n) := brutal_inclusionTerm_isIso K r n (by omega)
  exact HomologicalComplex.Hom.isIso_of_components _

theorem brutal_inclusion_map_quasiIsoAt_succ (K : CochainComplex C ℕ) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (r : ℤ) (n : ℕ) (hr : r ≤ (n : ℤ)) :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℕ)).map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)) (n + 1) := by
  let f := (F.mapHomologicalComplex (.up ℕ)).map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)
  have hcomp (k : ℕ) (hk : r ≤ (k : ℤ)) : IsIso (f.f k) := by
    have := brutal_inclusionTerm_isIso K r k hk
    change IsIso (F.map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r k))
    infer_instance
  have h0 := hcomp n hr
  have h1 := hcomp (n + 1) (by omega)
  have h2 := hcomp (n + 2) (by omega)
  apply (quasiIsoAt_iff' f n (n + 1) (n + 2)
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))).mpr
  let φ := (shortComplexFunctor' D (.up ℕ) n (n + 1) (n + 2)).map f
  have hφ0 : IsIso φ.τ₁ := h0
  have hφ1 : IsIso φ.τ₂ := h1
  have hφ2 : IsIso φ.τ₃ := h2
  have hφ : IsIso φ := ShortComplex.isIso_of_isIso φ
  exact ShortComplex.quasiIso_of_isIso φ

end

end OAI.AlgebraicGeometry.Comparison.Betti.Brutal.Complex
