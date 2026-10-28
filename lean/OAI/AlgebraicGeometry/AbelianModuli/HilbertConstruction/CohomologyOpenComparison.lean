import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.OpenComparisonSpan
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyKernelCokernelComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.IsomorphismKernelCokernel

/-! # Cohomology Open Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyOpenComparison

noncomputable section

/-! Coherent sheaves which agree on an open set have finite genuine cohomology simultaneously once finiteness is known on its closed complement. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem coefficientCohomologyFinite_iff_of_open_iso
    {X : Scheme.{u}} [IsLocallyNoetherian X] {R : Type u} [CommRing R] [IsNoetherianRing R]
    (c : R →+* Γ(X, ⊤)) (U : X.Opens) [QuasiCompact U.ι]
    (hsmall : ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsFiniteType →
      IsZero (Q.restrict U.ι) → CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c Q)
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType]
    (e : M.restrict U.ι ≅ N.restrict U.ι) :
    CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c M ↔ CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c N := by
  obtain ⟨K, a, b, hKq, hKt, ha, hb, _⟩ := Coherent.OpenComparisonSpan.exists_coherent_comparison_span U M N e
  have := hKq
  have := hKt
  have := ha
  have := hb
  have hmap {P Q : X.Modules} [P.IsQuasicoherent] [Q.IsQuasicoherent]
      [P.IsFiniteType] [Q.IsFiniteType] (g : P ⟶ Q)
      [IsIso ((restrictFunctor U.ι).map g)] :
      CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c P ↔ CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c Q := by
    exact CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.iff_of_kernel_cokernel c g
      (hsmall _ (Quasicoherent.Kernels.module_quasicoherent_kernel g) (Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType g)
        (Open.IsomorphismKernelCokernel.module_kernel_restrict_isZero_of_isIso U g))
      (hsmall _ (Quasicoherent.Cokernels.module_quasicoherent_cokernel g) (Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType g)
        (Open.IsomorphismKernelCokernel.module_cokernel_restrict_isZero_of_isIso U g))
  exact (hmap a).symm.trans (hmap b)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyOpenComparison
