import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Determinant

/-! # Top Exterior Determinant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorDeterminant

noncomputable section

/-! On the top exterior power, the map induced by an endomorphism is
multiplication by its native determinant. This is pure linear algebra. -/

variable {R V W ι : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [Fintype ι] [DecidableEq ι]

theorem alternating_eq_det_smulRight (b : Module.Basis ι R V)
    (ω : V [⋀^ι]→ₗ[R] W) : ω = b.det.smulRight (ω b) := by
  apply b.ext_alternating
  intro v hv
  let σ : Equiv.Perm ι := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
  change ω (b ∘ σ) = (b.det.smulRight (ω b)) (b ∘ σ)
  rw [AlternatingMap.map_perm, AlternatingMap.map_perm]
  congr 1
  change ω b = b.det b • ω b
  rw [b.det_self, one_smul]

theorem alternating_apply_eq_det_smul (b : Module.Basis ι R V)
    (ω : V [⋀^ι]→ₗ[R] W) (v : ι → V) : ω v = b.det v • ω b :=
  DFunLike.congr_fun (alternating_eq_det_smulRight b ω) v

theorem alternating_apply_comp (b : Module.Basis ι R V)
    (ω : V [⋀^ι]→ₗ[R] W) (f : Module.End R V) (v : ι → V) :
    ω (f ∘ v) = f.det • ω v := by
  rw [alternating_apply_eq_det_smul b ω (f ∘ v),
    alternating_apply_eq_det_smul b ω v, b.det_comp, mul_smul]

theorem map_eq_det_smul_of_basis {n : ℕ} (b : Module.Basis (Fin n) R V)
    (f : Module.End R V) :
    exteriorPower.map n f = f.det • LinearMap.id := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R n V)
  rintro w ⟨v, rfl⟩
  rw [exteriorPower.map_apply_ιMulti, LinearMap.smul_apply, LinearMap.id_apply]
  exact alternating_apply_comp b (exteriorPower.ιMulti R n) f v

theorem map_top_eq_det_smul {K : Type*} [Field K]
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : Module.End K M) :
    exteriorPower.map (Module.finrank K M) f = f.det • LinearMap.id :=
  map_eq_det_smul_of_basis (Module.finBasis K M) f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorDeterminant
