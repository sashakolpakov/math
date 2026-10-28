import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Extension Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ExtensionCoordinates.Construction

noncomputable section

/-! A continuous section of a surjective group homomorphism gives
topological product coordinates with its kernel. -/

def splitExtensionHomeomorph
    {A G : Type*} [Group A] [Group G] [TopologicalSpace A] [TopologicalSpace G]
    [IsTopologicalGroup A] [IsTopologicalGroup G]
    (q : G →* A) (s : A →* G) (hq : Continuous q) (hs : Continuous s)
    (hsection : ∀ a, q (s a) = a) : A × q.ker ≃ₜ G where
  toFun x := s x.1 * x.2.val
  invFun g := (q g, ⟨(s (q g))⁻¹ * g, by
    change q ((s (q g))⁻¹ * g) = 1
    rw [map_mul, map_inv, hsection, inv_mul_cancel]⟩)
  left_inv x := by
    have hx : q (s x.1 * x.2.val) = x.1 := by
      rw [map_mul, hsection, show q x.2.val = 1 from x.2.property, mul_one]
    apply Prod.ext
    · exact hx
    · apply Subtype.ext
      change (s (q (s x.1 * x.2.val)))⁻¹ * (s x.1 * x.2.val) = x.2.val
      rw [hx, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left (s (q g)) g
  continuous_toFun := (hs.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := hq.prodMk (((hs.comp hq).inv.mul continuous_id).subtype_mk _)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ExtensionCoordinates.Construction
