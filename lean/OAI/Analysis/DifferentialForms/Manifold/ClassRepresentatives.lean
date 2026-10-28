import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # Class Representatives -/

namespace OAI.Analysis.DifferentialForms.Manifold.ClassRepresentatives

noncomputable section

/-!
# Representatives of global manifold de Rham cohomology

These results use genuine smooth differential forms on the actual tangent
spaces of a smooth manifold, with the chart-independent exterior derivative.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

universe u v
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type v) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Every global de Rham class has a genuine closed-form representative. -/
theorem manifoldDeRhamFormClass_surjective (n : ℕ) :
    Function.Surjective (ManifoldDeRham.manifoldDeRhamFormClass E M n) := by
  exact (ManifoldDeRham.manifoldDeRhamFormQuotientIso E M n).toLinearEquiv.symm.surjective.comp
    (Submodule.mkQ_surjective (ManifoldDeRham.manifoldExactClosedForms E M n))

/-- Global closed forms represent the same class exactly when their difference
is an actual global exterior derivative. -/
theorem manifoldDeRhamFormClass_eq_iff (n : ℕ) (form other : ManifoldDeRham.manifoldClosedForms E M n) :
    ManifoldDeRham.manifoldDeRhamFormClass E M n form = ManifoldDeRham.manifoldDeRhamFormClass E M n other ↔
      ∃ ξ : Algebra.SmoothManifoldForm E M (n - 1),
        ManifoldDeRham.manifoldIncomingExteriorDerivative E M n ξ = form.val - other.val := by
  have hsub : (form - other).val = form.val - other.val := rfl
  simpa only [map_sub, sub_eq_zero, hsub] using
    ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff E M n (form - other)

/-- The categorical global cocycles identify with actual closed global forms. -/
def manifoldDeRhamClosedFormsIso (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCocycles E M n ≅ ModuleCat.of ℂ (ManifoldDeRham.manifoldClosedForms E M n) :=
  ShortComplex.cyclesMapIso (ManifoldDeRham.manifoldDeRhamFormShortComplexIso E M n) ≪≫
    (ManifoldDeRham.manifoldFormShortComplex E M n).moduleCatCyclesIso

/-- The global form-class map followed by the quotient identification is the
literal quotient map. -/
theorem manifoldDeRhamFormClass_comp_quotientIso (n : ℕ) :
    ModuleCat.ofHom (ManifoldDeRham.manifoldDeRhamFormClass E M n) ≫
        (ManifoldDeRham.manifoldDeRhamFormQuotientIso E M n).hom =
      ModuleCat.ofHom (ManifoldDeRham.manifoldExactClosedForms E M n).mkQ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact (ManifoldDeRham.manifoldDeRhamFormQuotientIso E M n).toLinearEquiv.apply_symm_apply
    ((ManifoldDeRham.manifoldExactClosedForms E M n).mkQ form)

/-- The concrete global form-class map agrees with the categorical class map
after the canonical identification of categorical cocycles with closed forms. -/
theorem manifoldDeRhamClosedFormsIso_comp_class (n : ℕ) :
    (manifoldDeRhamClosedFormsIso E M n).hom ≫
        ModuleCat.ofHom (ManifoldDeRham.manifoldDeRhamFormClass E M n) =
      ManifoldDeRham.manifoldDeRhamClass E M n := by
  apply (cancel_mono (ManifoldDeRham.manifoldDeRhamFormQuotientIso E M n).hom).mp
  rw [Category.assoc, manifoldDeRhamFormClass_comp_quotientIso]
  change
    (ShortComplex.cyclesMap (ManifoldDeRham.manifoldDeRhamFormShortComplexIso E M n).hom ≫
      (ManifoldDeRham.manifoldFormShortComplex E M n).moduleCatCyclesIso.hom) ≫
        (ManifoldDeRham.manifoldFormShortComplex E M n).moduleCatLeftHomologyData.π =
    ((ManifoldDeRham.manifoldDeRhamComplex E M).sc n).homologyπ ≫
      (ShortComplex.homologyMap (ManifoldDeRham.manifoldDeRhamFormShortComplexIso E M n).hom ≫
        (ManifoldDeRham.manifoldFormShortComplex E M n).moduleCatHomologyIso.hom)
  rw [Category.assoc, ← ShortComplex.π_moduleCatCyclesIso_hom,
    ← Category.assoc, ← ShortComplex.homologyπ_naturality, Category.assoc]

end

end OAI.Analysis.DifferentialForms.Manifold.ClassRepresentatives
