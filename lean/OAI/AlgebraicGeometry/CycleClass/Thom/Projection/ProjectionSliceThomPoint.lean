import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SlicePoint
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceNeighborhood

/-! # Projection Slice Thom Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.ProjectionSliceThomPoint.Constructions

noncomputable section

/-! Pullback of the actual sheet Thom class to an isolating normal slice is its canonical point class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SlicePoint.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductSimpleZero.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M L N E G W : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] [ChartedSpace W L]
  {c d : ℕ} {f : M → N} {x : M} {i : L → N × (Fin d → ℂ)} {y : L}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair W (Fin (c + d) → ℂ) i y)

local instance (priority := low) : ChartedSpace (G × (Fin d → ℂ)) (N × (Fin d → ℂ)) :=
  prodChartedSpace G N (Fin d → ℂ) (Fin d → ℂ)
local instance (priority := low) : ChartedSpace ((Fin c → ℂ) × (Fin d → ℂ))
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ)) :=
  prodChartedSpace (Fin c → ℂ) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Fin d → ℂ) (Fin d → ℂ)

variable [Nonempty (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P)]

theorem sliceToPair_Thom_pointClass
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G × (Fin d → ℂ))
      𝓘(ℂ, W × (Fin (c + d) → ℂ)))
    (hQa : ContMDiffOn 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, W × (Fin (c + d) → ℂ)) ω
      Q.ambientChart Q.ambientChart.source)
    (hi : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y)
    (hxy : (i y).1 = f x) (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f)
    (hip : Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y))
    (e : ((Fin c → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (c + d) → ℂ))
    (V : Opens (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ)))
    (z : V) (hz : z.val = (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2))
    (hV : Set.MapsTo (Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) (id : (Fin d → ℂ) → (Fin d → ℂ)))
      (V : Set _) Q.neighborhood)
    (hIso : ∀ a : V, Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id a.val ∈ Set.range i → a = z) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SliceNeighborhood.Constructions.sliceToPair P Q V hV)
      (SliceNeighborhood.Constructions.sliceToPair_mapsTo P Q V hV z hIso) (2 * (c + d)) Q.rationalClassFin =
        Open.ProductSimpleZero.Constructions.Class.localPointClass (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) e V z :=
  (SliceNeighborhood.Constructions.sliceToPair_Thom_pullback P Q V hV z hIso).trans
    (SlicePoint.Constructions.Class.sliceEquations_pointClass P Q hP hPi hQ hQa hi hxy hr hip e V z hz
      (SliceNeighborhood.Constructions.sliceEquationMap P Q V hV) (SliceNeighborhood.Constructions.sliceEquationMap_eq P Q V hV)
      (SliceNeighborhood.Constructions.sliceEquationMap_mapsTo P Q V hV z hIso))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.ProjectionSliceThomPoint.Constructions
