import OAI.AlgebraicGeometry.Cycles.Functoriality.AnalyticInverse
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Intrinsic Etale -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.IntrinsicEtale.Construction

noncomputable section

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- An etale algebra map induces a bijective differential on the genuine
smooth affine complex-point manifolds. -/
theorem mfderiv_smoothDomain_comap_bijective_of_etale
    {A B : Type*} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.Smooth ℂ A]
    [CommRing B] [Algebra ℂ B] [IsDomain B] [Algebra.Smooth ℂ B]
    (h : A →ₐ[ℂ] B) (hh : h.toRingHom.Etale) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Function.Bijective
      (mfderiv (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
        (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x) := by
  let := h.toRingHom.toAlgebra
  let : Algebra.Etale A B := hh
  have hfe : h.toRingHom.FormallyEtale := inferInstanceAs (Algebra.FormallyEtale A B)
  let L : (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) →L[ℂ]
      (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) :=
    mfderiv (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
      (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x
  have hinj : Function.Injective L :=
    EtaleDifferential.Construction.mfderiv_smoothDomain_comap_injective_of_unramified h hh.formallyUnramified x
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := L.toLinearMap) ?_).mp hinj⟩
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    EtaleDifferential.Construction.genericDifferentialRank_eq_of_formallyEtale h hfe

/-- A genuine affine scheme map is covered by affine source-target
squares obtained by pulling back a target affine open. -/
theorem exists_nativeAffineHom_affineReduction
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (φ : X ⟶ Y) [IsAffineHom φ.left]
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ (V : Y.left.Opens) (hV : IsAffineOpen V)
      (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))),
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X (φ.left ⁻¹ᵁ V)
        (hV.preimage φ.left) y = x := by
  obtain ⟨V, hV, y, hy⟩ :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x)
  have hmap : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ x ∈
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV) := ⟨y, hy⟩
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hmap
  have hx : x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X (φ.left ⁻¹ᵁ V)
      (hV.preimage φ.left)) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
    exact hmap
  obtain ⟨z, hz⟩ := hx
  exact ⟨V, hV, z, hz⟩

theorem nativeAffineOpenPullback_etale
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (φ : X ⟶ Y) [IsAffineHom φ.left] [Etale φ.left]
    (V : Y.left.Opens) (hV : IsAffineOpen V) :
    (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V).toRingHom.Etale := by
  change (φ.left.app V).hom.Etale
  rw [φ.left.app_eq_appLE]
  exact φ.left.etale_appLE hV (hV.preimage φ.left) le_rfl

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

/-- An affine etale map has bijective differential on the native complex
manifolds. In particular this applies to the finite etale support maps. -/
theorem mfderiv_nativeScheme_affineEtale_bijective
    (φ : X ⟶ Y) [IsAffineHom φ.left] [Etale φ.left] (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Bijective
      (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) x) := by
  obtain ⟨V, hV, y, hy⟩ := exists_nativeAffineHom_affineReduction φ x
  let W := φ.left ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage φ.left
  have hxW : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W := by
    have hr : x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X W hW) := ⟨y, hy⟩
    rwa [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  let : Nonempty W := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, hxW⟩⟩
  let : Nonempty V := ⟨⟨φ.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x), hxW⟩⟩
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V
  let B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X W
  let : IsDomain A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain Y V
  let : IsDomain B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X W
  let : Algebra.Smooth ℂ A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth Y V hV
  let : Algebra.Smooth ℂ B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X W hW
  let i := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X W hW
  let j := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV
  let h : A →ₐ[ℂ] B := ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V
  have hy' : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i y = x := hy
  rw [← hy']
  apply ComplexPoints.Analytic.IntrinsicOpenDifferential.bijective_mfderiv_of_comp
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i) y
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1).mdifferentiableAt one_ne_zero)
    ((ComplexPoints.Analytic.AffineOpenDifferential.contMDiff_affinePointMap B i 1).mdifferentiableAt one_ne_zero)
    (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective B i y)
  have hsquare : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A j ∘ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h := by
    funext z
    exact ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW z
  rw [hsquare, mfderiv_comp y
    ((ComplexPoints.Analytic.AffineOpenDifferential.contMDiff_affinePointMap A j 1).mdifferentiableAt one_ne_zero)
    ((ComplexPoints.Analytic.SmoothAffineMaps.contMDiff_smoothDomain_comap h 1).mdifferentiableAt one_ne_zero)]
  exact (ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective A j (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h y)).comp
    (mfderiv_smoothDomain_comap_bijective_of_etale h (nativeAffineOpenPullback_etale φ V hV) y)

/-- A finite etale morphism is locally an analytic diffeomorphism on its
actual complex points, with the native manifold structures. -/
theorem isLocalDiffeomorph_nativeScheme_affineEtale
    (φ : X ⟶ Y) [IsAffineHom φ.left] [Etale φ.left] :
    IsLocalDiffeomorph (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
  intro x
  exact AnalyticInverse.Construction.isLocalDiffeomorphAt_of_bijective_mfderiv _ (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ ω) x
    (mfderiv_nativeScheme_affineEtale_bijective φ x)

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.IntrinsicEtale.Construction
