import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.FiltrationPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.FiltrationBounds
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! # Abelian De Rham Filtration -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Actual extending endomorphisms and their rational Hecke sums preserve the native Hodge filtration. -/

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.Fil_eq_top (i : ℤ) (hi : i ≤ 0) : A.Fil i = ⊤ :=
  GeometricComparison.DeRham.FiltrationBounds.filtration_eq_top _ _ 1 i hi

theorem Geometry.AbelianH1Model.Fil_eq_bot (i : ℤ) (hi : 1 < i) : A.Fil i = ⊥ :=
  GeometricComparison.DeRham.FiltrationBounds.filtration_eq_bot _ _ 1 i hi

/-- The actual hypercohomological Hodge filtration, with proved bounds. -/
def Geometry.AbelianH1Model.finiteFiltration : Linear.FiniteFiltration ℚ_[q] A.DeRham where
  step := A.Fil
  antitone_step := AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration_antitone _ _ 1
  eventually_top := ⟨0, A.Fil_eq_top 0 le_rfl⟩
  eventually_bot := ⟨2, A.Fil_eq_bot 2 (by decide)⟩

@[simp]
theorem Geometry.AbelianH1Model.finiteFiltration_step (i : ℤ) : A.finiteFiltration.step i = A.Fil i := rfl

theorem Geometry.AbelianH1Model.deRhamPullback_preservesFil (f : A.ExtendingEndomorphism) (i : ℤ) :
    (A.Fil i).map (A.deRhamPullback f) ≤ A.Fil i :=
  GeometricComparison.DeRham.FiltrationPullback.filtration_pullback (A.localEndomorphism f) 1 i

theorem Geometry.AbelianH1Model.algebraicDeRhamPullback_preservesFil (f : A.ExtendingEndomorphism) (i : ℤ) :
    (A.algebraicFiltration i).map (A.algebraicDeRhamPullback f) ≤ A.algebraicFiltration i :=
  GeometricComparison.DeRham.FiltrationPullback.filtration_pullback f.generic.toMul.hom.hom 1 i

theorem Geometry.AbelianH1Model.deRhamHecke_preservesFil {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H) (h : H) (i : ℤ) :
    (A.Fil i).map (A.deRhamHecke ρ h) ≤ A.Fil i := by
  rintro _ ⟨x, hx, rfl⟩
  change ((ρ.presentation h).sum (fun f a => (a : ℚ_[q]) • A.deRhamPullback f)) x ∈ A.Fil i
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  exact (A.Fil i).sum_mem (fun f _ => (A.Fil i).smul_mem _
    (A.deRhamPullback_preservesFil f i ⟨x, hx, rfl⟩))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
