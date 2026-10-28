import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential
import Mathlib.Topology.LocalAtTarget

/-! # Open Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenImmersion.Constructions

noncomputable section

/-! An actual smooth algebraic immersion whose image is closed on a
specified analytic open gives a closed complex immersion on that open,
with its actual source preimage and native manifold structures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))

abbrev sourceOpen : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)),
    U.isOpen.preimage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map i)⟩

def restrictedMap : TopCat.of (sourceOpen i U) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun y => ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i y.val, y.property⟩,
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map i).comp continuous_subtype_val).subtype_mk _⟩

theorem restrictedMap_range : Set.range (restrictedMap i U) =
    Subtype.val ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, rfl⟩
  · rintro ⟨x, hxy⟩
    have hxU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x ∈ U := hxy.symm ▸ y.property
    exact ⟨⟨x, hxU⟩, Subtype.ext hxy⟩

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsImmersion i.left]

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "MY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ

omit [IsImmersion i.left] in
theorem restrictedMap_analytic : ContMDiff 𝓘(ℂ, MX) 𝓘(ℂ, MY) ω (restrictedMap i U) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U (restrictedMap i U) ω).mp
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map i ω).comp
    (show ContMDiff 𝓘(ℂ, MX) 𝓘(ℂ, MX) ω (Subtype.val : sourceOpen i U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) from
      contMDiff_subtype_val)

theorem restrictedMap_differential_injective (x : sourceOpen i U) :
    Function.Injective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, MY) (restrictedMap i U) x) := by
  have hv : MDifferentiableAt 𝓘(ℂ, MX) 𝓘(ℂ, MX)
      (Subtype.val : sourceOpen i U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) x :=
    (show ContMDiff 𝓘(ℂ, MX) 𝓘(ℂ, MX) 1 (Subtype.val : sourceOpen i U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) from
      contMDiff_subtype_val).mdifferentiableAt one_ne_zero
  have hd := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := MX) (F := MY) U (restrictedMap i U) x
  change mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, MY) (restrictedMap i U) x =
    mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, MY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ Subtype.val) x at hd
  rw [mfderiv_comp x (((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map i ω) x.val).mdifferentiableAt (by simp)) hv,
    Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal] at hd
  exact (congrArg (fun L : MX →L[ℂ] MY => Function.Injective L) hd).mpr
    (ComplexPoints.Analytic.IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective i x.val)

variable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (hclosed : IsClosed (Subtype.val ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) : Set U))

def restrictedImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (ClosedImmersion.Constructions.schemeManifold Y) U) p where
  regularComplexDimension := Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom
  regularAnalyticSpace := TopCat.of (sourceOpen i U)
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := restrictedMap i U
  holomorphic := restrictedMap_analytic i U
  differential_injective := restrictedMap_differential_injective i U
  closed := ⟨(U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)).restrictPreimage_isEmbedding
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion i), by
      rw [restrictedMap_range]
      exact hclosed⟩
  regularComplexDimension_add_codimension := hp

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenImmersion.Constructions
