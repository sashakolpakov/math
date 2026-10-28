import OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicHomeomorphInverse
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

/-! # Holomorphic Open Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles

noncomputable section

/-! An actual holomorphic open embedding with bijective differential
identifies its source biholomorphically with its open image. -/

open _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
open scoped _root_.Manifold ContDiff

variable {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
    (f : M → N) (hf : Topology.IsOpenEmbedding f)

def holomorphicOpenImage : Opens N := ⟨Set.range f, hf.isOpen_range⟩

def holomorphicOpenImageHomeomorph : M ≃ₜ holomorphicOpenImage f hf := hf.isEmbedding.toHomeomorph

theorem holomorphicOpenImageHomeomorph_val (x : M) :
    (holomorphicOpenImageHomeomorph f hf x).val = f x := rfl

variable (ha : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hd : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))

include ha in
omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem holomorphicOpenImageHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω (holomorphicOpenImageHomeomorph f hf) :=
  (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (holomorphicOpenImage f hf) (holomorphicOpenImageHomeomorph f hf) ω).mp ha

include hd in
omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem holomorphicOpenImageHomeomorph_differential (x : M) :
    Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) (holomorphicOpenImageHomeomorph f hf) x) :=
  (congrArg (fun l : E →L[ℂ] F => Function.Bijective l)
    (ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (holomorphicOpenImage f hf) (holomorphicOpenImageHomeomorph f hf) x)).mpr (hd x)

include ha hd in
omit [FiniteDimensional ℂ F] in
theorem holomorphicOpenImageHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ω (holomorphicOpenImageHomeomorph f hf).symm :=
  HolomorphicHomeomorphInverse.BundleCycles.holomorphicHomeomorph_inverse (holomorphicOpenImageHomeomorph f hf)
    (holomorphicOpenImageHomeomorph_analytic f hf ha) (holomorphicOpenImageHomeomorph_differential f hf hd)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles
