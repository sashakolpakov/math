import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Idempotent Group Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.IdempotentGroupProduct.Construction

noncomputable section

/-! An idempotent continuous group homomorphism splits its group
homeomorphically into its image and its kernel. -/

def idempotentGroupProductHomeomorph
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (q : G →* G) (hq : Continuous q) (hqq : ∀ g, q (q g) = q g) : q.range × q.ker ≃ₜ G where
  toFun x := x.1.val * x.2.val
  invFun g := (⟨q g, ⟨g, rfl⟩⟩, ⟨(q g)⁻¹ * g, by
    change q ((q g)⁻¹ * g) = 1
    rw [map_mul, map_inv, hqq, inv_mul_cancel]⟩)
  left_inv x := by
    have hx : q x.1.val = x.1.val := by
      obtain ⟨g, hg⟩ := x.1.property
      rw [← hg, hqq]
    have he : q (x.1.val * x.2.val) = x.1.val := by
      rw [map_mul, hx, show q x.2.val = 1 from x.2.property, mul_one]
    apply Prod.ext
    · exact Subtype.ext he
    · apply Subtype.ext
      change (q (x.1.val * x.2.val))⁻¹ * (x.1.val * x.2.val) = x.2.val
      rw [he, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left (q g) g
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (hq.subtype_mk _).prodMk ((hq.inv.mul continuous_id).subtype_mk _)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.IdempotentGroupProduct.Construction
