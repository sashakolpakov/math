import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-! # Components Range -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ComponentsRange.Constructions.Components

noncomputable section

/-!
# DegreeTwo: separating the components of a commutative Lie group

The image of a real vector group is divisible. If it is open, injectivity of
divisible abelian groups splits off a locally constant projection. Applied to
the constructed exponential, this will detect any extra analytic components.
-/

open scoped _root_.Topology

variable {V G : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup G]

/-- Every homomorphic image of a real vector group is divisible. -/
@[instance_reducible]
def rangeDivisible (p : V →+ G) : DivisibleBy p.range.toIntSubmodule ℤ := by
  apply divisibleByOfSMulRightSurj
  intro n hn x
  obtain ⟨v, hv⟩ := x.property
  refine ⟨⟨p ((n : ℝ)⁻¹ • v), ⟨_, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change n • p ((n : ℝ)⁻¹ • v) = x
  rw [← map_zsmul]
  have hdiv : n • ((n : ℝ)⁻¹ • v) = v := by
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul,
      mul_inv_cancel₀ (Int.cast_ne_zero.mpr hn), one_smul]
  rw [hdiv]
  exact hv

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- An open vector-group image is the kernel of a locally constant
endomorphism. This is an algebraic splitting, with local constancy proved
from the openness of its kernel. -/
theorem exists_locallyConstant_projection (p : V →+ G) (hp : IsOpen (p.range : Set G)) :
    ∃ h : G →+ G, IsLocallyConstant h ∧ ∀ x : G, h x = 0 ↔ x ∈ p.range := by
  let R := p.range.toIntSubmodule
  let : DivisibleBy R ℤ := rangeDivisible p
  let : Module.Injective ℤ R := (Module.Baer.of_divisible R).injective
  obtain ⟨r, hr⟩ := Module.Injective.out R.subtype R.subtype_injective (LinearMap.id : R →ₗ[ℤ] R)
  let h : G →+ G := (LinearMap.id - R.subtype.comp r).toAddMonoidHom
  have hk (x : G) : h x = 0 ↔ x ∈ p.range := by
    change x - (r x : G) = 0 ↔ x ∈ R
    rw [sub_eq_zero]
    constructor
    · intro hx
      exact hx ▸ (r x).property
    · intro hx
      have hh := congrArg Subtype.val (hr ⟨x, hx⟩)
      exact hh.symm
  refine ⟨h, ?_, hk⟩
  apply (IsLocallyConstant.iff_eventually_eq h).mpr
  intro x
  have hn : ∀ᶠ y in 𝓝 x, y - x ∈ p.range :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (hp.mem_nhds (by
        change x - x ∈ p.range
        rw [sub_self]
        exact p.range.zero_mem))
  filter_upwards [hn] with y hy
  have hh := (hk (y - x)).mpr hy
  rw [map_sub] at hh
  exact sub_eq_zero.mp hh

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ComponentsRange.Constructions.Components
