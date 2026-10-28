import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpen
import Mathlib.SetTheory.Cardinal.NatCard

/-! # Restricted Graph Smaller Fibers -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphSmallerFibers.Constructions

noncomputable section

/-! The actual graph restricted to two nested base opens has the original base differential and the full original fibers over points of the smaller open. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {L N E G F : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E L]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (g : L → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω g)
  (e : L → F) (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω e)
  (U P : Opens N) (hP : P ≤ U)

local instance (priority := low) (A : Opens N) : ChartedSpace (G × F) (A × F) :=
  prodChartedSpace G A F F

abbrev firstGraph : GraphOpenImmersion.Constructions.graphSourceOpen g hg U → U × F := GraphBaseRestriction.Constructions.restrictedGraph g e (U : Set N)

abbrev doubleSource := GraphOpenImmersion.Constructions.graphSourceOpen (firstGraph g hg e U) (GraphOpenImmersion.Constructions.restrictedGraph_analytic g hg U e he)
  (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P))

def doubleGraph : doubleSource g hg e he U P → P × F :=
  Product.SmallerOpen.Constructions.smallerGraph U P hP (firstGraph g hg e U) (GraphOpenImmersion.Constructions.restrictedGraph_analytic g hg U e he)

theorem doubleGraph_base (x : doubleSource g hg e he U P) :
    (doubleGraph g hg e he U P hP x).1.val = g x.val.val := rfl

theorem doubleGraph_projected_mfderiv (x : doubleSource g hg e he U P) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (Prod.fst ∘ doubleGraph g hg e he U P hP) x =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) g x.val.val := by
  have hv := (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (Subtype.val : GraphOpenImmersion.Constructions.graphSourceOpen g hg U → L) from contMDiff_subtype_val)
  have hw := (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (Subtype.val : doubleSource g hg e he U P → GraphOpenImmersion.Constructions.graphSourceOpen g hg U) from contMDiff_subtype_val)
  have hd := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := E) (F := G) P
    (Prod.fst ∘ doubleGraph g hg e he U P hP) x
  change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (Prod.fst ∘ doubleGraph g hg e he U P hP) x =
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G)
      ((g ∘ (Subtype.val : GraphOpenImmersion.Constructions.graphSourceOpen g hg U → L)) ∘
        (Subtype.val : doubleSource g hg e he U P → GraphOpenImmersion.Constructions.graphSourceOpen g hg U)) x at hd
  rw [mfderiv_comp x ((hg.comp hv).mdifferentiableAt (by simp)) (hw.mdifferentiableAt (by simp)),
    Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal, mfderiv_comp x.val (hg.mdifferentiableAt (by simp)) (hv.mdifferentiableAt (by simp)),
    Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal] at hd
  exact hd

def doubleGraph_fiberEquiv (u : P) :
    {z : doubleSource g hg e he U P | (doubleGraph g hg e he U P hP z).1 = u} ≃
      {y : L | g y = u.val} where
  toFun z := ⟨z.val.val.val, congrArg Subtype.val z.property⟩
  invFun y :=
    ⟨⟨⟨y.val, by change g y.val ∈ U; rw [y.property]; exact hP u.property⟩,
      by change g y.val ∈ P; rw [y.property]; exact u.property⟩, Subtype.ext y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem doubleGraph_fiber_card (u : P) :
    Nat.card {z : doubleSource g hg e he U P | (doubleGraph g hg e he U P hP z).1 = u} =
      Nat.card {y : L | g y = u.val} := Nat.card_congr (doubleGraph_fiberEquiv g hg e he U P hP u)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphSmallerFibers.Constructions
