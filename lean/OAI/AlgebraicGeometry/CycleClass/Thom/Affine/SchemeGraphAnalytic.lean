import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding
import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphLocalBound
import OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Scheme Graph Analytic -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

/-! Polynomial graph coordinates on actual smooth affine schemes form closed holomorphic immersions and have compact fiber bounds over a neighborhood for proper maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphLocalBound.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left] (g : X ⟶ Y)
  {n : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

def globalGraphCoordinates (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : Fin n → ℂ :=
  PresentationImmersion.Constructions.presentationCoordinates f (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X x)

def globalGraph (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y × (Fin n → ℂ) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x, globalGraphCoordinates f x)

theorem globalGraphCoordinates_continuous : Continuous (globalGraphCoordinates f) :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_coordinates (fun j => f (MvPolynomial.X j))).comp
    (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X).continuous

theorem globalGraphCoordinates_closedEmbedding (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (globalGraphCoordinates f) :=
  (PresentationImmersion.Constructions.presentationCoordinates_closedEmbedding f hf).comp (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X).isClosedEmbedding

theorem globalGraph_closedEmbedding [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (globalGraph g f) :=
  Closed.GraphEmbedding.Constructions.graph_closedEmbedding (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map g)
    (globalGraphCoordinates f) (globalGraphCoordinates_closedEmbedding f hf)

theorem globalGraph_localBound [WeaklyLocallyCompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (hg : IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    ∃ (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (K : Set (Fin n → ℂ)),
      x ∈ U ∧ IsCompact K ∧ ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g y ∈ U → globalGraphCoordinates f y ∈ K :=
  Proper.GraphLocalBound.Constructions.exists_local_compact_bound (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) hg (globalGraphCoordinates f)
    (globalGraphCoordinates_continuous f) x

variable [IsIntegral X.left] [Smooth X.hom]

local notation "ModelX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

theorem globalGraphCoordinates_analytic :
    ContMDiff 𝓘(ℂ, ModelX) 𝓘(ℂ, Fin n → ℂ) ω (globalGraphCoordinates f) :=
  (PresentationImmersion.Constructions.presentationCoordinates_analytic f ω).comp (SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_analytic X)

theorem globalGraphCoordinates_differential_injective (hf : Function.Surjective f)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Injective (mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, Fin n → ℂ) (globalGraphCoordinates f) x) := by
  change Function.Injective (mfderiv _ _ (PresentationImmersion.Constructions.presentationCoordinates f ∘ ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X) x)
  rw [mfderiv_comp x ((PresentationImmersion.Constructions.presentationCoordinates_analytic f ω).mdifferentiable (by simp) _)
    ((SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_analytic X).mdifferentiable (by simp) x)]
  exact (PresentationImmersion.Constructions.presentationCoordinates_differential_injective f hf _).comp
    (HolomorphicHomeomorph.Constructions.homeomorph_mfderiv_bijective (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X)
      ((SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_analytic X).mdifferentiable (by simp))
      ((SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_symm_analytic X).mdifferentiable (by simp)) x).injective

variable [IsIntegral Y.left] [Smooth Y.hom]
local notation "ModelY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ

local instance (priority := low) : ChartedSpace (ModelY × (Fin n → ℂ))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y × (Fin n → ℂ)) :=
  prodChartedSpace ModelY (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (Fin n → ℂ) (Fin n → ℂ)

theorem globalGraph_analytic :
    ContMDiff 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY × (Fin n → ℂ)) ω (globalGraph g f) := by
  rw [modelWithCornersSelf_prod]
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map g ω).prodMk (globalGraphCoordinates_analytic f)

theorem globalGraph_differential_injective (hf : Function.Surjective f) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Injective (mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY × (Fin n → ℂ)) (globalGraph g f) x) := by
  change Function.Injective (mfderiv _ _ (fun y => (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g y, globalGraphCoordinates f y)) x)
  rw [modelWithCornersSelf_prod,
    mfderiv_prodMk ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map g ω).mdifferentiable (by simp) x)
      ((globalGraphCoordinates_analytic f).mdifferentiable (by simp) x)]
  intro a b hab
  exact globalGraphCoordinates_differential_injective f hf x (congrArg Prod.snd hab)

end AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient

/-! The algebraic polynomial graph ambient is holomorphically the product of its actual native affine base with complex coordinate space, with the original base projection retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.AffineGraphAmbient.Constructions.Scheme OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine Y.left] (n : ℕ)

def nativeGraphHomeomorph :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin n) ℂ)) ≃ₜ
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y × (Fin n → ℂ)) :=
  (AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph Γ(Y.left, ⊤) n).trans
    ((ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph Y).symm.prodCongr (Homeomorph.refl (Fin n → ℂ)))

theorem nativeGraphHomeomorph_graph {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    (g : X ⟶ Y) (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    nativeGraphHomeomorph Y n (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeGraph.Constructions.globalGraphSchemeMap g f) x) = globalGraph g f x := by
  change ((ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph Y).symm
    (AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph Γ(Y.left, ⊤) n (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeGraph.Constructions.globalGraphSchemeMap g f) x)).1,
    (AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph Γ(Y.left, ⊤) n (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SchemeGraph.Constructions.globalGraphSchemeMap g f) x)).2) = _
  rw [SchemeGraph.Constructions.globalGraphSchemeMap_point]
  simp only [Homeomorph.symm_apply_apply]
  rfl

variable [IsIntegral Y.left] [Smooth Y.hom]

abbrev affineBaseModel := Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ Γ(Y.left, ⊤)) → ℂ
abbrev nativeGraphModel := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension
  (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin n) ℂ)).hom) → ℂ

local notation "MY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ

local instance (priority := low) : ChartedSpace (affineBaseModel Y × (Fin n → ℂ))
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints Γ(Y.left, ⊤) × (Fin n → ℂ)) :=
  prodChartedSpace (affineBaseModel Y) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints Γ(Y.left, ⊤)) (Fin n → ℂ) (Fin n → ℂ)
local instance (priority := low) : ChartedSpace (MY × (Fin n → ℂ)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y × (Fin n → ℂ)) :=
  prodChartedSpace MY (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (Fin n → ℂ) (Fin n → ℂ)

theorem nativeGraphHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, nativeGraphModel Y n) 𝓘(ℂ, MY × (Fin n → ℂ)) ω (nativeGraphHomeomorph Y n) := by
  have hp : ContMDiff 𝓘(ℂ, affineBaseModel Y × (Fin n → ℂ)) 𝓘(ℂ, MY × (Fin n → ℂ)) ω
      ((ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph Y).symm.prodCongr (Homeomorph.refl (Fin n → ℂ))) := by
    simp only [modelWithCornersSelf_prod]
    exact (SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_symm_analytic Y).prodMap
      (show ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω id from contMDiff_id)
  exact hp.comp (AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph_analytic Γ(Y.left, ⊤) n)

theorem nativeGraphHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, MY × (Fin n → ℂ)) 𝓘(ℂ, nativeGraphModel Y n) ω (nativeGraphHomeomorph Y n).symm := by
  have hp : ContMDiff 𝓘(ℂ, MY × (Fin n → ℂ)) 𝓘(ℂ, affineBaseModel Y × (Fin n → ℂ)) ω
      ((ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph Y).prodCongr (Homeomorph.refl (Fin n → ℂ))) := by
    simp only [modelWithCornersSelf_prod]
    exact (SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_analytic Y).prodMap
      (show ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω id from contMDiff_id)
  exact (AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph_symm_analytic Γ(Y.left, ⊤) n).comp hp

theorem nativeGraphHomeomorph_dimension (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension
      (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin n) ℂ)).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom + n :=
  (AffineGraphAmbient.Constructions.Scheme.schemeGraphHomeomorph_dimension Γ(Y.left, ⊤) n (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph Y y)).trans
    (congrArg (fun k => k + n) (SmoothAffineGlobalCoordinates.Constructions.affineNative_modelDimension Y y).symm)

end AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient

end

end OAI
