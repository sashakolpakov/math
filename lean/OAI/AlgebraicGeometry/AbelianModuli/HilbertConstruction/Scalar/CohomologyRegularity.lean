import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.QuotientComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroCycles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedRegularModuleVanishing

/-! # Cohomology Regularity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CohomologyRegularity

noncomputable section

/-! Vanishing in the preceding degree after scalar reduction forces the scalar to act injectively on cohomology. With finite support in its zero locus, the original cohomology then vanishes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R]

theorem cochain_homology_succ_regular_of_reduction_exact
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hreg : ∀ q, IsSMulRegular (C.X q) r) (n : ℕ)
    (hprev : (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (R ⧸ Ideal.span {r}) C).ExactAt n) :
    IsSMulRegular (C.homology (n + 1)) r := by
  let S := QuotientComplex.cochainScalarQuotientSequence C r
  have hS : S.ShortExact := QuotientComplex.cochainScalarQuotientSequence_shortExact C r hreg
  have hz : IsZero (S.X₃.homology n) :=
    (HomologicalComplex.homologyMapIso (QuotientComplex.cochainScalarQuotientTensorIso C r) n).isZero_iff.mpr
      hprev.isZero_homology
  have hmono : Mono (HomologicalComplex.homologyMap S.f (n + 1)) :=
    (hS.homology_exact₁ n (n + 1) rfl).mono_g (hz.eq_zero_of_src _)
  change Mono (HomologicalComplex.homologyMap (r • 𝟙 C) (n + 1)) at hmono
  rw [CoefficientCech.HomologyScalars.cochainHomologyMap_smul, HomologicalComplex.homologyMap_id] at hmono
  exact (ModuleCat.mono_iff_injective (r • 𝟙 (C.homology (n + 1)))).mp hmono

theorem cochain_homology_zero_regular
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hreg : IsSMulRegular (C.X 0) r) : IsSMulRegular (C.homology 0) r := by
  have hk : IsSMulRegular (C.d 0 1).hom.ker r := hreg.submodule _ r
  let e := ((Cochain.ZeroCycles.CochainZeroCycles.cyclesIso C).symm ≪≫ C.isoHomologyπ₀).toLinearEquiv
  exact (e.isSMulRegular_congr r).mp hk

theorem cochain_homology_succ_zero_of_supported_reduction_exact
    [IsNoetherianRing R] (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (I : Ideal R) (r : R) (hr : r ∈ I)
    (hreg : ∀ q, IsSMulRegular (C.X q) r) (n : ℕ)
    [Module.Finite R (C.homology (n + 1))]
    (hSupport : Module.support R (C.homology (n + 1)) ⊆ PrimeSpectrum.zeroLocus (I : Set R))
    (hprev : (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (R ⧸ Ideal.span {r}) C).ExactAt n) :
    IsZero (C.homology (n + 1)) := by
  have : Subsingleton (C.homology (n + 1)) :=
    SupportedRegularModuleVanishing.finiteSupportedModule_subsingleton_of_regularElement I hSupport r hr
      (cochain_homology_succ_regular_of_reduction_exact C r hreg n hprev)
  exact ModuleCat.isZero_of_subsingleton _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CohomologyRegularity
