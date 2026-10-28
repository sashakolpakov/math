import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Projection

/-! # Projector Range Free -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectorRangeFree.CM

noncomputable section

/-! The range of an actual idempotent on a finite free module over a
local ring is finite free. This will be applied to coefficient projectors. -/

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Free R M]

theorem range_free (p : Module.End R M) (hp : p * p = p) : Module.Free R p.range := by
  have hr : p.rangeRestrict.comp p.range.subtype = LinearMap.id := by
    ext x
    obtain ⟨y, hy⟩ := x.property
    change p x.val = x.val
    rw [← hy]
    exact LinearMap.congr_fun hp y
  have : Module.Flat R p.range := Module.Flat.of_retract p.range.subtype p.rangeRestrict hr
  exact Module.free_of_flat_of_isLocalRing

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectorRangeFree.CM
