import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations
import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticLocalInverseAt

/-! # Slice Local Inverse -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceLocalInverse.Constructions

noncomputable section

/-! The actual normal equations on a projection slice have a local analytic inverse. -/

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticLocalInverseAt.Constructions

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

theorem sliceEquations_localInverse
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G × (Fin d → ℂ))
      𝓘(ℂ, W × (Fin (c + d) → ℂ)))
    (hQa : ContMDiffOn 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, W × (Fin (c + d) → ℂ)) ω
      Q.ambientChart Q.ambientChart.source)
    (hi : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y)
    (hxy : (i y).1 = f x) (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f)
    (hip : Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y)) :
    IsLocalDiffeomorphAt 𝓘(ℂ, (Fin c → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ) ω
      (SliceEquations.Constructions.sliceEquations P Q) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2) := by
  let : IsManifold 𝓘(ℂ, (Fin c → ℂ) × (Fin d → ℂ)) ω
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ)) := Product.Immersion.Constructions.productModel_isManifold
  exact AnalyticLocalInverseAt.Constructions.isLocalDiffeomorphAt_of_bijective_mfderiv (SliceEquations.Constructions.sliceEquations P Q)
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2)
    (SliceEquations.Constructions.sliceEquations_analyticAt P Q hPi hQa hxy)
    (SliceEquations.Constructions.sliceEquations_mfderiv_bijective P Q hP hPi hQ hi hxy hr hip)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceLocalInverse.Constructions
