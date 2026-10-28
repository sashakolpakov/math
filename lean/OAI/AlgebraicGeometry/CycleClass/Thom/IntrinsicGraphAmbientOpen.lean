import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientEmbedding
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion

/-! # Intrinsic Graph Ambient Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic

noncomputable section

/-! The actual polynomial graph ambient above an open subset of the original variety has explicit holomorphic product coordinates, with its original base and fiber coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left] (d : ℕ)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))

local notation "MN" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ

local instance (priority := low) : ChartedSpace (MN × (Fin d → ℂ)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N × (Fin d → ℂ)) :=
  prodChartedSpace MN (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, MN × (Fin d → ℂ)) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold
local instance (priority := low) : ChartedSpace (MN × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace MN U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, MN × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

abbrev graphAmbientOpen := GraphOpenImmersion.Constructions.graphSourceOpen (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d) (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_analytic j d) (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen U)

variable (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

include hU in
omit [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral N.left] [Smooth N.hom] [IsOpenImmersion j.left] in
theorem productOpen_subset_range : (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (F := Fin d → ℂ) U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N × (Fin d → ℂ))) ⊆
    Set.range (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d) := by
  rw [IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_range]
  exact fun _ hx => ⟨hU hx, Set.mem_univ _⟩

def graphAmbientHomeomorph : graphAmbientOpen j d U ≃ₜ (U × (Fin d → ℂ)) :=
  (Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d) (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_analytic j d) (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_openEmbedding j d)
    (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen U) (productOpen_subset_range j d U hU)).trans (Open.ProductHomeomorphAnalytic.Constructions.openBaseProductHomeomorph U)

theorem graphAmbientHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphModel Y d) 𝓘(ℂ, MN × (Fin d → ℂ)) ω (graphAmbientHomeomorph j d U hU) :=
  (Open.ProductHomeomorphAnalytic.Constructions.baseProductHomeomorph_analytic (G := MN) (F := Fin d → ℂ) U).comp
    (Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph_analytic (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d) (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_analytic j d) (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_openEmbedding j d)
      (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen U) (productOpen_subset_range j d U hU))

theorem graphAmbientHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, MN × (Fin d → ℂ)) 𝓘(ℂ, Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphModel Y d) ω (graphAmbientHomeomorph j d U hU).symm :=
  (Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph_symm_analytic (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d) (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_analytic j d) (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_openEmbedding j d)
    (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen U) (productOpen_subset_range j d U hU) (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_mfderiv_bijective j d)).comp
      (Open.ProductHomeomorphAnalytic.Constructions.baseProductHomeomorph_symm_analytic (G := MN) (F := Fin d → ℂ) U)

theorem graphAmbientHomeomorph_base (x : graphAmbientOpen j d U) :
    (graphAmbientHomeomorph j d U hU x).1.val = (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d x.val).1 := rfl

theorem graphAmbientHomeomorph_coordinate (x : graphAmbientOpen j d U) :
    (graphAmbientHomeomorph j d U hU x).2 = (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d x.val).2 := rfl

omit [IsOpenImmersion j.left] in
theorem graphPoint_mem_ambientOpen {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    (g : X ⟶ Y) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x ∈ graphAmbientOpen j d U ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x) ∈ U := by
  change (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x)).1 ∈ U ↔ _
  rw [IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_graph]

theorem graphAmbientHomeomorph_graph {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    (g : X ⟶ Y) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x) ∈ U) :
    graphAmbientHomeomorph j d U hU
      ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x, (graphPoint_mem_ambientOpen j d U g f x).mpr hx⟩ =
        (⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x), hx⟩, Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x) := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_graph j d g f x)
  · exact congrArg (Prod.snd : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N × (Fin d → ℂ) → (Fin d → ℂ))
      (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap_graph j d g f x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic
