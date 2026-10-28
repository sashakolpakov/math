import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearChartKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.EquationComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealBundle

/-! # Linear Divisor Ideal Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearDivisorIdealIso.BundleCycles

noncomputable section

/-! Regular linear homogeneous divisors have isomorphic actual
ideal sheaves, with no reducedness assumption on the coefficient ring. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {A B C σ τ υ : Type} [CommRing A] [CommRing B] [CommRing C]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    [SetLike υ C] [AddSubgroupClass υ C]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → υ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
    (hcover : ∀ x : Proj 𝒜, ∃ v : A, v ∈ 𝒜 1 ∧ x ∈ Proj.basicOpen 𝒜 v)
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hSurjF : Function.Surjective f) (t : A) (ht : t ∈ 𝒜 1) (hregT : IsRegular t)
    (hkT : RingHom.ker f.toRingHom = Ideal.span {t})

include hcover hSurjF ht hregT hkT in
theorem projectiveLinearDivisor_regularPrincipalImageIdeals :
    Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals (Proj.map f hf) := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp (LinearChartBasis.BundleCycles.projectiveLinearChartBasis_isBasis 𝒜 hcover)
    (show x ∈ (⊤ : (Proj 𝒜).Opens) from trivial)
  exact ⟨⟨U, hU.1⟩, hxU, LinearChartBasis.BundleCycles.projectiveLinearChartSection 𝒜 t ht ⟨U, hU⟩,
    LinearChartBasis.BundleCycles.projectiveLinearChartSection_regular 𝒜 t ht hregT ⟨U, hU⟩,
    LinearChartKernel.BundleCycles.projectiveLinearChartSection_kernel f hf hSurjF t ht hkT ⟨U, hU⟩⟩

variable (g : 𝒜 →+*ᵍ 𝒞) (hg : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (hSurjG : Function.Surjective g) (u : A) (hu : u ∈ 𝒜 1) (hregU : IsRegular u)
    (hkU : RingHom.ker g.toRingHom = Ideal.span {u})

def projectiveLinearDivisorIdealIso : Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule (Proj.map f hf) ≅ Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule (Proj.map g hg) :=
  Cartier.EquationComparison.BundleCycles.cartierEquationComparisonIso (Proj.map f hf) (Proj.map g hg)
    (LinearChartBasis.BundleCycles.projectiveLinearChartBasis 𝒜) (LinearChartBasis.BundleCycles.projectiveLinearChartBasis_isBasis 𝒜 hcover)
    (LinearChartBasis.BundleCycles.projectiveLinearChartSection 𝒜 t ht) (LinearChartBasis.BundleCycles.projectiveLinearChartSection 𝒜 u hu)
    (LinearChartBasis.BundleCycles.projectiveLinearChartSection_regular 𝒜 t ht hregT) (LinearChartBasis.BundleCycles.projectiveLinearChartSection_regular 𝒜 u hu hregU)
    (LinearChartKernel.BundleCycles.projectiveLinearChartSection_kernel f hf hSurjF t ht hkT)
    (LinearChartKernel.BundleCycles.projectiveLinearChartSection_kernel g hg hSurjG u hu hkU)
    (LinearChartBasis.BundleCycles.projectiveLinearChartSection_cross 𝒜 t u ht hu)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearDivisorIdealIso.BundleCycles
