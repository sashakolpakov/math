import OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicEtale
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion

/-! # Etale Graph Open Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions

noncomputable section

/-! Graphs of genuine étale maps followed by an immersion have injective projected differential on every base open, independently of their fiber coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw
open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicEtale.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {L M N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral L.left] [Smooth L.hom]
  [IsIntegral M.left] [Smooth M.hom] [IsIntegral N.left] [Smooth N.hom]
  (g : L ⟶ M) [IsAffineHom g.left] [Etale g.left] (j : M ⟶ N) [IsImmersion j.left]

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension L.hom) → ℂ
local notation "MN" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ

def etaleBase : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g

omit [IsAffineHom g.left] [Etale g.left] [IsImmersion j.left] in
theorem etaleBase_analytic : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, MN) ω (etaleBase g j) :=
  (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω).comp (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map g ω)

theorem etaleBase_differential_injective (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints L) :
    Function.Injective (mfderiv 𝓘(ℂ, ML) 𝓘(ℂ, MN) (etaleBase g j) x) := by
  unfold etaleBase
  rw [mfderiv_comp x ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω).mdifferentiable (by simp) _)
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map g ω).mdifferentiable (by simp) x)]
  exact (ComplexPoints.Analytic.IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective j _).comp
    (ProperImage.IntrinsicEtale.Constructions.Construction.mfderiv_nativeScheme_affineEtale_bijective g x).injective

variable (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) {d : ℕ} (e : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints L → (Fin d → ℂ))

local instance (priority := low) : ChartedSpace (MN × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace MN U (Fin d → ℂ) (Fin d → ℂ)

def openGraph : GraphOpenImmersion.Constructions.graphSourceOpen (etaleBase g j) (etaleBase_analytic g j) U → U × (Fin d → ℂ) :=
  GraphBaseRestriction.Constructions.restrictedGraph (etaleBase g j) e (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))

omit [IsAffineHom g.left] [Etale g.left] [IsImmersion j.left] in
theorem openGraph_analytic (he : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω e) :
    ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, MN × (Fin d → ℂ)) ω (openGraph g j U e) :=
  GraphOpenImmersion.Constructions.restrictedGraph_analytic (etaleBase g j) (etaleBase_analytic g j) U e he

theorem openGraph_projected_differential_injective
    (x : GraphOpenImmersion.Constructions.graphSourceOpen (etaleBase g j) (etaleBase_analytic g j) U) :
    Function.Injective (mfderiv 𝓘(ℂ, ML) 𝓘(ℂ, MN) (Prod.fst ∘ openGraph g j U e) x) :=
  OpenImmersion.Constructions.Raw.restrictedBase_differential_injective (etaleBase g j) (etaleBase_analytic g j) U
    (etaleBase_differential_injective g j) x

theorem openGraph_differential_injective (he : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω e)
    (x : GraphOpenImmersion.Constructions.graphSourceOpen (etaleBase g j) (etaleBase_analytic g j) U) :
    Function.Injective (mfderiv 𝓘(ℂ, ML) 𝓘(ℂ, MN × (Fin d → ℂ)) (openGraph g j U e) x) := by
  have hp := openGraph_projected_differential_injective g j U e x
  have hf : MDifferentiableAt 𝓘(ℂ, MN × (Fin d → ℂ)) 𝓘(ℂ, MN)
      (Prod.fst : U × (Fin d → ℂ) → U) (openGraph g j U e x) := by
    rw [modelWithCornersSelf_prod]
    exact (show ContMDiff (𝓘(ℂ, MN).prod 𝓘(ℂ, Fin d → ℂ)) 𝓘(ℂ, MN) ω
      (Prod.fst : U × (Fin d → ℂ) → U) from contMDiff_fst).mdifferentiableAt (by simp)
  rw [mfderiv_comp x hf ((openGraph_analytic g j U e he).mdifferentiable (by simp) x)] at hp
  intro a b hab
  apply hp
  exact congrArg (mfderiv 𝓘(ℂ, MN × (Fin d → ℂ)) 𝓘(ℂ, MN)
    (Prod.fst : U × (Fin d → ℂ) → U) (openGraph g j U e x)) hab

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions
