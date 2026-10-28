import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel

/-! # Slice Differential -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential.Constructions

noncomputable section

/-! The differential of the actual normal slice is a right inverse of the actual normal differential. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Slice.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

variable {M N E G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

omit [NormedSpace ℂ E] in
theorem normalSliceAmbient_origin :
    SliceAnalytic.Constructions.normalSliceAmbientMap P (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P) = f x :=
  congrArg Subtype.val (Slice.Constructions.Class.normalSlice_origin P)

omit [NormedSpace ℂ E] in
theorem ambientNormal_comp_slice :
    NormalPair.TangentKernel.Constructions.ambientNormal P ∘ SliceAnalytic.Constructions.normalSliceAmbientMap P =
      (Subtype.val : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P → (Fin c → ℂ)) := by
  funext u
  exact congrArg (fun z : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P => z.1.val)
    (Slice.Constructions.Class.normalSlice_first P u)

theorem normalSlice_mfderiv_rightInverse
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin c → ℂ)))
    (hPi : ContMDiffOn 𝓘(ℂ, E × (Fin c → ℂ)) 𝓘(ℂ, G) ω
      P.ambientChart.symm P.ambientChart.target) :
    (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, Fin c → ℂ) (NormalPair.TangentKernel.Constructions.ambientNormal P) (f x)).comp
      (mfderiv 𝓘(ℂ, Fin c → ℂ) 𝓘(ℂ, G) (SliceAnalytic.Constructions.normalSliceAmbientMap P)
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P)) = ContinuousLinearMap.id ℂ (Fin c → ℂ) := by
  have hn : MDifferentiableAt 𝓘(ℂ, G) 𝓘(ℂ, Fin c → ℂ)
      (NormalPair.TangentKernel.Constructions.ambientNormal P) (SliceAnalytic.Constructions.normalSliceAmbientMap P (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P)) := by
    rw [normalSliceAmbient_origin]
    exact (ContinuousLinearMap.snd ℂ E (Fin c → ℂ)).mdifferentiableAt.comp (f x)
      (hP.mdifferentiableAt P.point_mem_source)
  have hs := ((SliceAnalytic.Constructions.normalSliceAmbient_analytic P hPi) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P)).mdifferentiableAt
    (show (ω : ℕ∞ω) ≠ 0 by simp)
  have hd := mfderiv_comp (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P) hn hs
  rw [ambientNormal_comp_slice P, Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal, normalSliceAmbient_origin P] at hd
  exact hd.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDifferential.Constructions
