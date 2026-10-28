import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SliceDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.TransverseProjectionLinear

/-! # Slice Equations -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations.Constructions.NormalDerivative

/-! Normal equations restrict invertibly to an actual slice of a sheet with injective projection. -/

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SliceDifferential.Constructions

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

theorem normal_slice_linear_injective
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G × (Fin d → ℂ))
      𝓘(ℂ, W × (Fin (c + d) → ℂ)))
    (hi : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y)
    (hxy : (i y).1 = f x) (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f)
    (hip : Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y)) :
    Function.Injective
      ((mfderiv 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ)
        (NormalPair.TangentKernel.Constructions.ambientNormal Q) (i y)).comp
        ((mfderiv 𝓘(ℂ, Fin c → ℂ) 𝓘(ℂ, G) (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P)
          (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P)).prodMap (ContinuousLinearMap.id ℂ (Fin d → ℂ)))) := by
  have hproj := Product.SliceDifferential.Constructions.projection_mfderiv i y hi
  have hip' : Function.Injective ((ContinuousLinearMap.fst ℂ G (Fin d → ℂ)).comp
      (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y)) := hproj ▸ hip
  have hii : Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y) := by
    intro a b hab
    apply hip'
    exact congrArg (ContinuousLinearMap.fst ℂ G (Fin d → ℂ)) hab
  have hpd : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y := by
    rw [modelWithCornersSelf_prod] at hi
    exact hi.fst
  have hz := NormalPair.TangentKernel.Constructions.Map.normal_comp_zero_of_range P (Prod.fst ∘ i) y hP hpd hxy hr
  rw [hproj] at hz
  exact TransverseProjectionLinear.Constructions.normal_slice_injective
    (k := ℂ) (A := G) (F := Fin d → ℂ) (U := Fin c → ℂ) (W := W)
    (V := Fin (c + d) → ℂ)
    (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, Fin c → ℂ) (NormalPair.TangentKernel.Constructions.ambientNormal P) (f x)).toLinearMap
    (mfderiv 𝓘(ℂ, Fin c → ℂ) 𝓘(ℂ, G) (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P)
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P)).toLinearMap
    (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y).toLinearMap
    (mfderiv 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ)
      (NormalPair.TangentKernel.Constructions.ambientNormal Q) (i y)).toLinearMap
    (congrArg ContinuousLinearMap.toLinearMap (Normal.SliceDifferential.Constructions.normalSlice_mfderiv_rightInverse P hP hPi))
    (NormalPair.TangentKernel.Constructions.ambientNormal_ker Q hQ hi hii)
    (congrArg ContinuousLinearMap.toLinearMap hz) hip'

theorem normal_slice_linear_bijective
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G × (Fin d → ℂ))
      𝓘(ℂ, W × (Fin (c + d) → ℂ)))
    (hi : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y)
    (hxy : (i y).1 = f x) (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f)
    (hip : Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y)) :
    Function.Bijective
      ((mfderiv 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ)
        (NormalPair.TangentKernel.Constructions.ambientNormal Q) (i y)).comp
        ((mfderiv 𝓘(ℂ, Fin c → ℂ) 𝓘(ℂ, G) (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P)
          (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P)).prodMap (ContinuousLinearMap.id ℂ (Fin d → ℂ)))) := by
  have h := normal_slice_linear_injective P Q hP hPi hQ hi hxy hr hip
  refine ⟨h, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℂ) (V := (Fin c → ℂ) × (Fin d → ℂ)) (V₂ := Fin (c + d) → ℂ)
    (by simp only [Module.finrank_prod, Module.finrank_fin_fun])
    (f := ((mfderiv 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ)
      (NormalPair.TangentKernel.Constructions.ambientNormal Q) (i y)).comp
      ((mfderiv 𝓘(ℂ, Fin c → ℂ) 𝓘(ℂ, G) (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P)
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P)).prodMap (ContinuousLinearMap.id ℂ (Fin d → ℂ)))).toLinearMap)).mp h

end AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations.Constructions.NormalDerivative

namespace AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations.Constructions

/-! The actual normal equations on a projection slice are holomorphic and have invertible differential. -/

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SliceDifferential.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations.Constructions.NormalDerivative

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

def sliceEquations : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ) → (Fin (c + d) → ℂ) :=
  NormalPair.TangentKernel.Constructions.ambientNormal Q ∘ Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) (id : (Fin d → ℂ) → (Fin d → ℂ))

omit [NormedSpace ℂ E] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [ChartedSpace G N]
  [NormedSpace ℂ W] [FiniteDimensional ℂ W] [ChartedSpace W L] [TopologicalSpace L] in
theorem sliceProduct_image (hxy : (i y).1 = f x) :
    Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) (id : (Fin d → ℂ) → (Fin d → ℂ))
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2) = i y :=
  Prod.ext ((Normal.SliceDifferential.Constructions.normalSliceAmbient_origin P).trans hxy.symm) rfl

omit [NormedSpace ℂ E] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [ChartedSpace G N]
  [NormedSpace ℂ W] [FiniteDimensional ℂ W] [ChartedSpace W L] [TopologicalSpace L] in
theorem sliceEquations_zero (hxy : (i y).1 = f x) :
    sliceEquations P Q (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2) = 0 := by
  change NormalPair.TangentKernel.Constructions.ambientNormal Q (Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2)) = 0
  rw [sliceProduct_image P hxy]
  exact congrArg Prod.snd Q.point_coordinates

omit [TopologicalSpace L] [FiniteDimensional ℂ G] [FiniteDimensional ℂ W] [ChartedSpace W L] in
theorem sliceEquations_analyticAt
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQa : ContMDiffOn 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, W × (Fin (c + d) → ℂ)) ω
      Q.ambientChart Q.ambientChart.source)
    (hxy : (i y).1 = f x) :
    ContMDiffAt 𝓘(ℂ, (Fin c → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ) ω
      (sliceEquations P Q) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2) := by
  have hs : ContMDiff 𝓘(ℂ, (Fin c → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, G × (Fin d → ℂ)) ω
      (Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) (id : (Fin d → ℂ) → (Fin d → ℂ))) := by
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    exact (Normal.SliceAnalytic.Constructions.normalSliceAmbient_analytic P hPi).prodMap contMDiff_id
  have hq := (hQa (i y) Q.point_mem_source).contMDiffAt
    (Q.ambientChart.open_source.mem_nhds Q.point_mem_source)
  have hn : ContMDiffAt 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ) ω
      (NormalPair.TangentKernel.Constructions.ambientNormal Q) (Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2)) := by
    rw [sliceProduct_image P hxy]
    exact (ContinuousLinearMap.snd ℂ W (Fin (c + d) → ℂ)).contMDiff.contMDiffAt.comp (i y) hq
  exact hn.comp (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2) (hs _)

theorem sliceEquations_mfderiv_bijective
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target)
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G × (Fin d → ℂ))
      𝓘(ℂ, W × (Fin (c + d) → ℂ)))
    (hi : MDifferentiableAt 𝓘(ℂ, W) 𝓘(ℂ, G × (Fin d → ℂ)) i y)
    (hxy : (i y).1 = f x) (hr : Set.range (Prod.fst ∘ i) ⊆ Set.range f)
    (hip : Function.Injective (mfderiv 𝓘(ℂ, W) 𝓘(ℂ, G) (Prod.fst ∘ i) y)) :
    Function.Bijective (mfderiv 𝓘(ℂ, (Fin c → ℂ) × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ)
      (sliceEquations P Q) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2)) := by
  have hs := (Normal.SliceAnalytic.Constructions.normalSliceAmbient_analytic P hPi).mdifferentiable (show (ω : ℕ∞ω) ≠ 0 by simp)
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P)
  have hn : MDifferentiableAt 𝓘(ℂ, G × (Fin d → ℂ)) 𝓘(ℂ, Fin (c + d) → ℂ)
      (NormalPair.TangentKernel.Constructions.ambientNormal Q) (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P), (i y).2) := by
    change MDifferentiableAt _ _ _ (Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2))
    rw [sliceProduct_image P hxy]
    exact (ContinuousLinearMap.snd ℂ W (Fin (c + d) → ℂ)).mdifferentiableAt.comp (i y)
      (hQ.mdifferentiableAt Q.point_mem_source)
  have hd := Product.SliceDifferential.Constructions.product_slice_comp_mfderiv (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) (NormalPair.TangentKernel.Constructions.ambientNormal Q)
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P) (i y).2 hs hn
  change mfderiv _ _ (sliceEquations P Q) _ = _ at hd
  change mfderiv _ _ (sliceEquations P Q) _ =
    (mfderiv _ _ (NormalPair.TangentKernel.Constructions.ambientNormal Q) (Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, (i y).2))).comp _ at hd
  rw [sliceProduct_image P hxy] at hd
  rw [hd]
  exact NormalDerivative.normal_slice_linear_bijective P Q hP hPi hQ hi hxy hr hip

end AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations.Constructions

end

end OAI
