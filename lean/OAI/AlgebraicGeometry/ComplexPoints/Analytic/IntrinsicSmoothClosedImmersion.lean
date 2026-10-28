import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth

/-! # Intrinsic Smooth Closed Immersion -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion

noncomputable section

/-!
# Differentials of closed immersions on native complex scheme points

The affine reduction uses the actual inverse image of a target affine open,
the actual pullback on its section rings, and the established native analytic
point topologies and manifold structures.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Pullback on sections, with precisely the scalar structures induced by the
two native structure maps over the complex base. -/
def nativeAffineOpenPullback (φ : X ⟶ Y) (V : Y.left.Opens) :
    SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V →ₐ[ℂ]
      SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V) where
  __ := (φ.left.app V).hom
  commutes' r := by
    change (φ.left.app V).hom (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap Y.hom V r) =
      Foundations.Scheme.SpecScalarTransport.specSectionScalarMap X.hom (φ.left ⁻¹ᵁ V) r
    have h := congrArg (fun f : ℂ →+* Γ(X.left, φ.left ⁻¹ᵁ V) => f r)
      (Foundations.Scheme.ClosedImmersionDimension.specSectionScalarMap_app φ.left Y.hom V)
    simpa only [RingHom.comp_apply, φ.w] using h

/-- A closed immersion makes this actual affine section pullback surjective. -/
theorem nativeAffineOpenPullback_surjective (φ : X ⟶ Y)
    [IsClosedImmersion φ.left] (V : Y.left.Opens) (hV : IsAffineOpen V) :
    Function.Surjective (nativeAffineOpenPullback φ V) :=
  φ.left.app_surjective V hV

/-- The native affine section pullback represents the original scheme morphism
on the inverse image of a genuine affine target open. -/
theorem nativeAffineOpenPullback_scheme_square (φ : X ⟶ Y)
    (V : Y.left.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen (φ.left ⁻¹ᵁ V)) :
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
        (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))
        (nativeAffineOpenPullback φ V) ≫
      SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV =
    SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X (φ.left ⁻¹ᵁ V) hW ≫ φ := by
  apply Over.OverMorphism.ext
  change Spec.map (φ.left.app V) ≫ hV.fromSpec = hW.fromSpec ≫ φ.left
  rw [φ.left.app_eq_appLE]
  exact IsAffineOpen.SpecMap_appLE_fromSpec φ.left hV hW le_rfl

/-- The preceding scheme square gives an exact identity of ordinary native
point maps, not merely agreement on the underlying Zariski points. -/
theorem nativeAffineOpenPullback_point_square (φ : X ⟶ Y)
    (V : Y.left.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen (φ.left ⁻¹ᵁ V))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))) :
    SchemePointHomeomorphs.schemeComplexPoints.map φ
        (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X (φ.left ⁻¹ᵁ V) hW x) =
      SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (nativeAffineOpenPullback φ V) x) := by
  change SchemePointHomeomorphs.schemeComplexPoints.map φ
      (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap _ _ x) =
    SchemePointHomeomorphs.schemeComplexPoints.affinePointMap _ _ _
  rw [← SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp,
    ← nativeAffineOpenPullback_scheme_square φ V hV hW,
    SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap]

/-- Every point of a closed immersion is covered by the actual affine inverse
image of a target affine neighborhood. -/
theorem exists_nativeClosedImmersion_affineReduction (φ : X ⟶ Y)
    [IsClosedImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ (V : Y.left.Opens) (hV : IsAffineOpen V)
      (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))),
      SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X (φ.left ⁻¹ᵁ V)
        (hV.preimage φ.left) y = x := by
  obtain ⟨V, hV, y, hy⟩ :=
    SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift Y (SchemePointHomeomorphs.schemeComplexPoints.map φ x)
  have hmap : SchemePointHomeomorphs.schemeComplexPoints.map φ x ∈
      Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap Y V hV) := ⟨y, hy⟩
  rw [SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hmap
  have hx : x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X (φ.left ⁻¹ᵁ V)
      (hV.preimage φ.left)) := by
    rw [SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
    exact hmap
  obtain ⟨z, hz⟩ := hx
  exact ⟨V, hV, z, hz⟩

section DifferentialTransfer

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₁ E₂ F₁ F₂ : Type*}
variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
variable [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
variable [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
variable [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {P M Q N : Type*}
variable [TopologicalSpace P] [ChartedSpace E₁ P]
variable [TopologicalSpace M] [ChartedSpace E₂ M]
variable [TopologicalSpace Q] [ChartedSpace F₁ Q]
variable [TopologicalSpace N] [ChartedSpace F₂ N]

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of a differential descends through an actual commuting square
when the source chart differential is surjective and the other two are
injective. This is the manifold chain rule and injectivity of a composition. -/
theorem injective_mfderiv_of_commuting_square
    (f : M → N) (a : P → M) (b : Q → N) (g : P → Q) (x : P)
    (hsquare : f ∘ a = b ∘ g)
    (hf : MDifferentiableAt (𝓘(𝕜, E₂)) (𝓘(𝕜, F₂)) f (a x))
    (ha : MDifferentiableAt (𝓘(𝕜, E₁)) (𝓘(𝕜, E₂)) a x)
    (hb : MDifferentiableAt (𝓘(𝕜, F₁)) (𝓘(𝕜, F₂)) b (g x))
    (hg : MDifferentiableAt (𝓘(𝕜, E₁)) (𝓘(𝕜, F₁)) g x)
    (hasurj : Function.Surjective (mfderiv (𝓘(𝕜, E₁)) (𝓘(𝕜, E₂)) a x))
    (hbinj : Function.Injective (mfderiv (𝓘(𝕜, F₁)) (𝓘(𝕜, F₂)) b (g x)))
    (hginj : Function.Injective (mfderiv (𝓘(𝕜, E₁)) (𝓘(𝕜, F₁)) g x)) :
    Function.Injective (mfderiv (𝓘(𝕜, E₂)) (𝓘(𝕜, F₂)) f (a x)) := by
  have h := mfderiv_congr (I := 𝓘(𝕜, E₁)) (I' := 𝓘(𝕜, F₂)) (x := x) hsquare
  rw [mfderiv_comp x hf ha, mfderiv_comp x hb hg] at h
  have hinj : Function.Injective
      ((mfderiv (𝓘(𝕜, E₂)) (𝓘(𝕜, F₂)) f (a x)).comp
        (mfderiv (𝓘(𝕜, E₁)) (𝓘(𝕜, E₂)) a x)) := by
    rw [h]
    exact hbinj.comp hginj
  exact Function.Injective.of_comp_right
    (f := mfderiv (𝓘(𝕜, E₂)) (𝓘(𝕜, F₂)) f (a x))
    (g := mfderiv (𝓘(𝕜, E₁)) (𝓘(𝕜, E₂)) a x) hinj hasurj

end DifferentialTransfer

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

/-- An actual closed immersion of smooth integral complex schemes has
injective complex differential on its native complex-valued points. -/
theorem mfderiv_nativeScheme_closedImmersion_injective (φ : X ⟶ Y)
    [IsClosedImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Injective
      (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) := by
  obtain ⟨V, hV, y, hy⟩ := exists_nativeClosedImmersion_affineReduction φ x
  let W := φ.left ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage φ.left
  have hxW : SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W := by
    have hr : x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X W hW) := ⟨y, hy⟩
    rwa [SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  let : Nonempty W := ⟨⟨SchemePointHomeomorphs.schemeComplexPoints.underlying x, hxW⟩⟩
  let : Nonempty V := ⟨⟨φ.left (SchemePointHomeomorphs.schemeComplexPoints.underlying x), hxW⟩⟩
  let A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V
  let B := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X W
  let : IsDomain A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain Y V
  let : IsDomain B := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X W
  let : Algebra.Smooth ℂ A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth Y V hV
  let : Algebra.Smooth ℂ B := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X W hW
  let i := SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X W hW
  let j := SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV
  let h : A →ₐ[ℂ] B := nativeAffineOpenPullback φ V
  have hy' : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i y = x := hy
  rw [← hy']
  refine injective_mfderiv_of_commuting_square
    (SchemePointHomeomorphs.schemeComplexPoints.map φ) (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i)
    (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A j) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) y ?_
    ((IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1).mdifferentiableAt one_ne_zero)
    ((AffineOpenDifferential.contMDiff_affinePointMap B i 1).mdifferentiableAt one_ne_zero)
    ((AffineOpenDifferential.contMDiff_affinePointMap A j 1).mdifferentiableAt one_ne_zero)
    ((SmoothAffineMaps.contMDiff_smoothDomain_comap h 1).mdifferentiableAt one_ne_zero)
    (AffineOpenDifferential.mfderiv_affinePointMap_bijective B i y).2
    (AffineOpenDifferential.mfderiv_affinePointMap_bijective A j (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h y)).1
    (SmoothClosedImmersion.mfderiv_smoothDomain_comap_injective_of_surjective h
      (nativeAffineOpenPullback_surjective φ V hV) y)
  funext z
  exact nativeAffineOpenPullback_point_square φ V hV hW z

/-- The corresponding injectivity on the underlying real tangent spaces is
also a theorem of the genuine closed immersion. -/
theorem real_mfderiv_nativeScheme_closedImmersion_injective (φ : X ⟶ Y)
    [IsClosedImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Injective
      (mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) := by
  obtain ⟨V, hV, y, hy⟩ := exists_nativeClosedImmersion_affineReduction φ x
  let W := φ.left ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage φ.left
  have hxW : SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W := by
    have hr : x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X W hW) := ⟨y, hy⟩
    rwa [SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  let : Nonempty W := ⟨⟨SchemePointHomeomorphs.schemeComplexPoints.underlying x, hxW⟩⟩
  let : Nonempty V := ⟨⟨φ.left (SchemePointHomeomorphs.schemeComplexPoints.underlying x), hxW⟩⟩
  let A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V
  let B := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X W
  let : IsDomain A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain Y V
  let : IsDomain B := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X W
  let : Algebra.Smooth ℂ A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth Y V hV
  let : Algebra.Smooth ℂ B := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X W hW
  let i := SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X W hW
  let j := SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV
  let h : A →ₐ[ℂ] B := nativeAffineOpenPullback φ V
  have hy' : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i y = x := hy
  rw [← hy']
  refine injective_mfderiv_of_commuting_square
    (SchemePointHomeomorphs.schemeComplexPoints.map φ) (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i)
    (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A j) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) y ?_
    ((IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map φ 1).mdifferentiableAt one_ne_zero)
    ((AffineOpenDifferential.real_contMDiff_affinePointMap B i 1).mdifferentiableAt one_ne_zero)
    ((AffineOpenDifferential.real_contMDiff_affinePointMap A j 1).mdifferentiableAt one_ne_zero)
    ((SmoothAffineMaps.real_contMDiff_smoothDomain_comap h 1).mdifferentiableAt one_ne_zero)
    (AffineOpenDifferential.real_mfderiv_affinePointMap_bijective B i y).2
    (AffineOpenDifferential.real_mfderiv_affinePointMap_bijective A j (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h y)).1
    (SmoothClosedImmersion.real_mfderiv_smoothDomain_comap_injective_of_surjective h
      (nativeAffineOpenPullback_surjective φ V hV) y)
  funext z
  exact nativeAffineOpenPullback_point_square φ V hV hW z

/-- A genuine closed immersion of smooth integral complex schemes induces a
closed point embedding with injective complex differential everywhere. -/
theorem nativeScheme_closedImmersion_closedEmbedding_and_injective_differential
    (φ : X ⟶ Y) [IsClosedImmersion φ.left] :
    Topology.IsClosedEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map φ) ∧
      ∀ x : SchemePointHomeomorphs.schemeComplexPoints X,
        Function.Injective
          (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) :=
  ⟨SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion φ,
    mfderiv_nativeScheme_closedImmersion_injective φ⟩

/-- The same statement for the established underlying real smooth manifolds. -/
theorem nativeScheme_closedImmersion_closedEmbedding_and_injective_real_differential
    (φ : X ⟶ Y) [IsClosedImmersion φ.left] :
    Topology.IsClosedEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map φ) ∧
      ∀ x : SchemePointHomeomorphs.schemeComplexPoints X,
        Function.Injective
          (mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) :=
  ⟨SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion φ,
    real_mfderiv_nativeScheme_closedImmersion_injective φ⟩

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion
