import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphFiber

/-! # Etale Local Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions

noncomputable section

/-! An étale graph needs its holomorphic fiber coordinates only on the actual source preimage of the chosen base open. Its projected differential and fibers remain the genuine ones. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphFiber.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {L M N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral L.left] [Smooth L.hom]
  [IsIntegral M.left] [Smooth M.hom] [IsIntegral N.left] [Smooth N.hom]
  (g : L ⟶ M) [IsAffineHom g.left] [Etale g.left] (j : M ⟶ N) [IsImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) {d : ℕ}

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension L.hom) → ℂ
local notation "MN" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ

local instance (priority := low) : ChartedSpace (MN × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace MN U (Fin d → ℂ) (Fin d → ℂ)

variable (e : GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U → Fin d → ℂ)

def localGraph : GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U → U × (Fin d → ℂ) :=
  fun x => (GraphOpenImmersion.Constructions.restrictedBase (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U x, e x)

omit [IsAffineHom g.left] [Etale g.left] [IsImmersion j.left] in
theorem localGraph_analytic (he : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω e) :
    ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, MN × (Fin d → ℂ)) ω (localGraph g j U e) := by
  rw [modelWithCornersSelf_prod]
  exact (GraphOpenImmersion.Constructions.restrictedBase_analytic (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U).prodMk he

theorem localGraph_projected_differential_injective
    (x : GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U) :
    Function.Injective (mfderiv 𝓘(ℂ, ML) 𝓘(ℂ, MN) (Prod.fst ∘ localGraph g j U e) x) :=
  EtaleGraphOpenImmersion.Constructions.openGraph_projected_differential_injective g j U (fun _ => (0 : Fin d → ℂ)) x

theorem localGraph_differential_injective (he : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω e)
    (x : GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U) :
    Function.Injective (mfderiv 𝓘(ℂ, ML) 𝓘(ℂ, MN × (Fin d → ℂ)) (localGraph g j U e) x) := by
  have hp := localGraph_projected_differential_injective g j U e x
  have hf : MDifferentiableAt 𝓘(ℂ, MN × (Fin d → ℂ)) 𝓘(ℂ, MN)
      (Prod.fst : U × (Fin d → ℂ) → U) (localGraph g j U e x) := by
    rw [modelWithCornersSelf_prod]
    exact (show ContMDiff (𝓘(ℂ, MN).prod 𝓘(ℂ, Fin d → ℂ)) 𝓘(ℂ, MN) ω
      (Prod.fst : U × (Fin d → ℂ) → U) from contMDiff_fst).mdifferentiableAt (by simp)
  have hd := mfderiv_comp x hf ((localGraph_analytic g j U e he).mdifferentiableAt (by simp))
  have hc := (congrArg (fun A : ML →L[ℂ] MN => Function.Injective A) hd).mp hp
  intro v w hvw
  exact hc (congrArg (mfderiv 𝓘(ℂ, MN × (Fin d → ℂ)) 𝓘(ℂ, MN)
    (Prod.fst : U × (Fin d → ℂ) → U) (localGraph g j U e x)) hvw)

def localGraph_fiberEquiv (u : U) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M) (hy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j y = u.val) :
    {x : GraphOpenImmersion.Constructions.graphSourceOpen (EtaleGraphOpenImmersion.Constructions.etaleBase g j) (EtaleGraphOpenImmersion.Constructions.etaleBase_analytic g j) U | (localGraph g j U e x).1 = u} ≃
      {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints L | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = y} :=
  RestrictedGraphFiber.Constructions.graphFiberEquiv (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion j).injective (fun _ => (0 : Fin d → ℂ))
    (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) u y hy

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
