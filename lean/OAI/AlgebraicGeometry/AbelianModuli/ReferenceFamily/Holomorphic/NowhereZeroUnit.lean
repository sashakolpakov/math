import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! # Nowhere Zero Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.NowhereZeroUnit

noncomputable section

/-! A nowhere-zero holomorphic function is an actual unit, with its
pointwise reciprocal as a holomorphic inverse. -/

open scoped _root_.Manifold ContDiff

def holomorphicUnitOfNowhereZero (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    (f : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M)) (hf : ∀ x, f x ≠ 0) :
    (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M))ˣ where
  val := f
  inv := ⟨fun x => (f x)⁻¹, f.property.inv₀ hf⟩
  val_inv := ContMDiffMap.ext (fun x => mul_inv_cancel₀ (hf x))
  inv_val := ContMDiffMap.ext (fun x => inv_mul_cancel₀ (hf x))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.NowhereZeroUnit
