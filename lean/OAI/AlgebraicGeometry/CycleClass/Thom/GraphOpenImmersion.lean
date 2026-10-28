import OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Graph Open Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions

noncomputable section

/-! Restricting a holomorphic graph over a base open preserves holomorphy and injective differential. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X N E G F : Type} [TopologicalSpace X] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E X]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (g : X → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω g) (U : Opens N)

abbrev graphSourceOpen : Opens X := ⟨g ⁻¹' (U : Set N), U.isOpen.preimage hg.continuous⟩

def restrictedBase : graphSourceOpen g hg U → U := fun x => ⟨g x.val, x.property⟩

theorem restrictedBase_analytic :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω (restrictedBase g hg U) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U (restrictedBase g hg U) ω).mp
  exact hg.comp (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (Subtype.val : graphSourceOpen g hg U → X) from contMDiff_subtype_val)

theorem restrictedGraph_analytic (e : X → F) (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω e) :
    letI : ChartedSpace (G × F) (U × F) := prodChartedSpace G U F F
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G × F) ω
      (fun z : graphSourceOpen g hg U => (GraphBaseRestriction.Constructions.restrictedGraph g e (U : Set N) z : U × F)) := by
  let : ChartedSpace (G × F) (U × F) := prodChartedSpace G U F F
  rw [modelWithCornersSelf_prod]
  exact (restrictedBase_analytic g hg U).prodMk (he.comp
    (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (Subtype.val : graphSourceOpen g hg U → X) from contMDiff_subtype_val))

theorem restrictedCoordinates_mfderiv (e : X → F) (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω e)
    (x : graphSourceOpen g hg U) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) (e ∘ (Subtype.val : graphSourceOpen g hg U → X)) x =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x.val := by
  have hv := (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) 1
    (Subtype.val : graphSourceOpen g hg U → X) from contMDiff_subtype_val).mdifferentiableAt
      (x := x) one_ne_zero
  rw [mfderiv_comp x ((he x.val).mdifferentiableAt (by simp)) hv, Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal]
  rfl

theorem restrictedGraph_differential_injective (e : X → F)
    (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω e)
    (hei : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x))
    (x : graphSourceOpen g hg U) :
    letI : ChartedSpace (G × F) (U × F) := prodChartedSpace G U F F
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G × F)
      (fun z : graphSourceOpen g hg U => (GraphBaseRestriction.Constructions.restrictedGraph g e (U : Set N) z : U × F)) x) := by
  let : ChartedSpace (G × F) (U × F) := prodChartedSpace G U F F
  have hb := (restrictedBase_analytic g hg U).mdifferentiable (show (ω : ℕ∞ω) ≠ 0 by simp) x
  have hc := (he.comp (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (Subtype.val : graphSourceOpen g hg U → X) from contMDiff_subtype_val)).mdifferentiable
      (show (ω : ℕ∞ω) ≠ 0 by simp) x
  change Function.Injective (mfderiv _ _ (fun a => (restrictedBase g hg U a,
    (e ∘ (Subtype.val : graphSourceOpen g hg U → X)) a)) x)
  rw [modelWithCornersSelf_prod, mfderiv_prodMk hb hc]
  intro a b hab
  apply hei x.val
  have h := congrArg Prod.snd hab
  change (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) (e ∘ (Subtype.val : graphSourceOpen g hg U → X)) x) a =
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) (e ∘ (Subtype.val : graphSourceOpen g hg U → X)) x) b at h
  rwa [restrictedCoordinates_mfderiv g hg U e he x] at h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
