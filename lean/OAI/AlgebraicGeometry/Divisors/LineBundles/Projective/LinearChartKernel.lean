import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearChartBasis
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalSectionKernel

/-! # Linear Chart Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearChartKernel.BundleCycles

noncomputable section

/-! The homogeneous equation generates the actual ideal on
the affine basis subordinate to linear projective charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {A B σ τ : Type} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hSurj : Function.Surjective f) (t : A) (ht : t ∈ 𝒜 1)
    (hk : RingHom.ker f.toRingHom = Ideal.span {t})

include hSurj hk in
theorem projectiveLinearChartSection_kernel (U : LinearChartBasis.BundleCycles.projectiveLinearChartBasis 𝒜) :
    RingHom.ker ((Proj.map f hf).app U.1).hom = Ideal.span {LinearChartBasis.BundleCycles.projectiveLinearChartSection 𝒜 t ht U} := by
  let i := Proj.map f hf
  let : IsClosedImmersion i := ClosedImmersion.BundleCycles.projectiveMap_isClosedImmersion f hf hSurj
  let v := LinearChartBasis.BundleCycles.projectiveLinearChartDenominator 𝒜 U
  let hv := LinearChartBasis.BundleCycles.projectiveLinearChartDenominator_degree 𝒜 U
  let V : (Proj 𝒜).affineOpens := ⟨Proj.basicOpen 𝒜 v, Proj.isAffineOpen_basicOpen 𝒜 v hv (by decide)⟩
  let hUV : U.1 ≤ V.1 := LinearChartBasis.BundleCycles.projectiveLinearChartDenominator_bound 𝒜 U
  have hSrc : i.ker.ideal V = Ideal.span {CoordinateSectionMap.BundleCycles.projectiveCoordinateSection 𝒜 v t hv ht} :=
    (Scheme.Hom.ker_apply i V).trans (PrincipalSectionKernel.BundleCycles.projectivePrincipalSection_kernel f hf v t hv ht hk)
  have hMap := i.ker.map_ideal (U := ⟨U.1, U.2.1⟩) (V := V) hUV
  have hTarget := Scheme.Hom.ker_apply i ⟨U.1, U.2.1⟩
  refine hTarget.symm.trans (hMap.symm.trans ((congrArg (Ideal.map ((Proj 𝒜).presheaf.map (homOfLE hUV).op).hom) hSrc).trans ?_))
  rw [Ideal.map_span, Set.image_singleton]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LinearChartKernel.BundleCycles
