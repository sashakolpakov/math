import Mathlib.Data.Finsupp.Basic

/-! # Family Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FamilyMap.BundleCycles

/-! # LineBundleCycles: summing an actual mapped finite family -/

theorem finiteFamily_sum_map {A M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (F : A →₀ M) (L : M →+ N) :
    (F.mapRange L L.map_zero).sum (fun _ n => n) = L (F.sum (fun _ m => m)) := by
  rw [Finsupp.sum_mapRange_index (fun _ => rfl), map_finsuppSum]

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FamilyMap.BundleCycles
