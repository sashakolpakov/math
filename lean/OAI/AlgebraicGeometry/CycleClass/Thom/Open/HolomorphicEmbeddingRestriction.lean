import OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph
import OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Holomorphic Embedding Restriction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions

/-! An actual holomorphic open embedding with bijective differential identifies every open subset of its image with its source preimage, holomorphically in both directions. -/

open _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  (j : M → N) (hj : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω j)
  (hji : Topology.IsOpenEmbedding j) (U : Opens N) (hU : (U : Set N) ⊆ Set.range j)

def restrictedHomeomorph : GraphOpenImmersion.Constructions.graphSourceOpen j hj U ≃ₜ U := hji.isEmbedding.homeomorphOfSubsetRange hU

theorem restrictedHomeomorph_val (x : GraphOpenImmersion.Constructions.graphSourceOpen j hj U) :
    (restrictedHomeomorph j hj hji U hU x).val = j x.val := rfl

theorem restrictedHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω (restrictedHomeomorph j hj hji U hU) :=
  GraphOpenImmersion.Constructions.restrictedBase_analytic j hj U

theorem restrictedHomeomorph_mfderiv (x : GraphOpenImmersion.Constructions.graphSourceOpen j hj U) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (restrictedHomeomorph j hj hji U hU) x =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) j x.val := by
  have hv := (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (Subtype.val : GraphOpenImmersion.Constructions.graphSourceOpen j hj U → M) from contMDiff_subtype_val)
  have hd := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := E) (F := G) U
    (restrictedHomeomorph j hj hji U hU) x
  change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (restrictedHomeomorph j hj hji U hU) x =
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (j ∘ (Subtype.val : GraphOpenImmersion.Constructions.graphSourceOpen j hj U → M)) x at hd
  rw [mfderiv_comp x (hj.mdifferentiableAt (by simp)) (hv.mdifferentiableAt (by simp)), InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal] at hd
  exact hd

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ G]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, G) ω N]

theorem restrictedHomeomorph_symm_analytic
    (hd : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) j x)) :
    ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, E) ω (restrictedHomeomorph j hj hji U hU).symm := by
  apply HolomorphicHomeomorph.Constructions.homeomorph_symm_analytic (restrictedHomeomorph j hj hji U hU)
    (restrictedHomeomorph_analytic j hj hji U hU)
  intro x
  exact (congrArg (fun L : E →L[ℂ] G => Function.Bijective L)
    (restrictedHomeomorph_mfderiv j hj hji U hU x)).mpr (hd x.val)

end AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift

/-! A genuine open subscheme containing every retained ambient fiber gives a canonical holomorphic lift of any source parametrization on that retained open. The lift preserves the actual ambient map and every coordinate bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {L X S N : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral L.left] [Smooth L.hom] [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral S.left] [Smooth S.hom] [IsIntegral N.left] [Smooth N.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left] (r : L ⟶ S) (f : S ⟶ N)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension L.hom) → ℂ
local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "MS" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ
local notation "MN" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ

def liftBase : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map r

theorem liftBase_analytic : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, MN) ω (liftBase r f) :=
  (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f ω).comp (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map r ω)

abbrev ambientPreimage := GraphOpenImmersion.Constructions.graphSourceOpen (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f ω) U
abbrev liftSource := GraphOpenImmersion.Constructions.graphSourceOpen (liftBase r f) (liftBase_analytic r f) U

def sourceToAmbientPreimage : liftSource r f U → ambientPreimage f U :=
  fun x => ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map r x.val, x.property⟩

theorem sourceToAmbientPreimage_analytic :
    ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, MS) ω (sourceToAmbientPreimage r f U) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (ambientPreimage f U) (sourceToAmbientPreimage r f U) ω).mp
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map r ω).comp
    (show ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, ML) ω (Subtype.val : liftSource r f U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints L) from
      contMDiff_subtype_val)

variable (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
  Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

def sourceHomeomorph : GraphOpenImmersion.Constructions.graphSourceOpen (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ω)
    (ambientPreimage f U) ≃ₜ ambientPreimage f U :=
  restrictedHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ω)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion a) (ambientPreimage f U) hcover

def sourceLift : liftSource r f U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
  Subtype.val ∘ (sourceHomeomorph a f U hcover).symm ∘ sourceToAmbientPreimage r f U

theorem sourceLift_analytic : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, MX) ω (sourceLift a r f U hcover) := by
  have he := restrictedHomeomorph_symm_analytic (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ω)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion a) (ambientPreimage f U) hcover
    (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective a)
  exact (show ContMDiff 𝓘(ℂ, MX) 𝓘(ℂ, MX) ω
      (Subtype.val : GraphOpenImmersion.Constructions.graphSourceOpen (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ω)
        (ambientPreimage f U) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) from contMDiff_subtype_val).comp
    (he.comp (sourceToAmbientPreimage_analytic r f U))

theorem sourceLift_commutes (x : liftSource r f U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a (sourceLift a r f U hcover x) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map r x.val :=
  congrArg Subtype.val ((sourceHomeomorph a f U hcover).apply_symm_apply (sourceToAmbientPreimage r f U x))

theorem sourceLift_bound {F : Type} (e : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → F) (K : Set F)
    (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U → e y ∈ K)
    (x : liftSource r f U) : e (sourceLift a r f U hcover x) ∈ K := by
  apply hb
  rw [sourceLift_commutes]
  exact x.property

end AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift

end

end OAI
