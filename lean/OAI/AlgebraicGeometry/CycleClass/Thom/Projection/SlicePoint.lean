import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceLocalInverse
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductSimpleZero

/-! # Slice Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SlicePoint.Constructions.Class

noncomputable section

/-! The actual restricted normal equations of a projection sheet have canonical point class on an isolating open. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceLocalInverse.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions.Product
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.InverseChartChange.Constructions
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

theorem sliceEquations_pointClass
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
    (g : TopCat.of V ⟶ TopCat.of (Fin (c + d) → ℂ))
    (hg : (g : V → (Fin (c + d) → ℂ)) = SliceEquations.Constructions.sliceEquations P Q ∘ Subtype.val)
    (hp : Set.MapsTo g ({z}ᶜ) ({0}ᶜ)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hp (2 * (c + d))
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (c + d)) =
        Open.ProductSimpleZero.Constructions.Class.localPointClass (p := c) (d := d) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) e V z := by
  have hlocal := SliceLocalInverse.Constructions.sliceEquations_localInverse P Q hP hPi hQ hQa hi hxy hr hip
  have hlocal' : IsLocalDiffeomorphAt 𝓘(ℂ, (Fin c → ℂ) × (Fin d → ℂ))
      𝓘(ℂ, Fin (c + d) → ℂ) ω (SliceEquations.Constructions.sliceEquations P Q) z.val := hz.symm ▸ hlocal
  apply Open.ProductSimpleZero.Constructions.Class.simpleZero_class (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) e (SliceEquations.Constructions.sliceEquations P Q) V z hlocal' g hg
  · exact (congrFun hg z).trans ((congrArg (SliceEquations.Constructions.sliceEquations P Q) hz).trans
      (SliceEquations.Constructions.sliceEquations_zero P Q hxy))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SlicePoint.Constructions.Class
