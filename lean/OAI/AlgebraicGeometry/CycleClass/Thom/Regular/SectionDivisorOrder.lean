import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative

/-! # Section Divisor Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SectionDivisorOrder.Constructions

noncomputable section

/-! A nonzero regular section has nonzero scheme order at every prime
divisor outside its full basic open of invertibility. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder.Constructions

variable (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, Opens.mem_top _⟩⟩

variable (s : Γ(X, ⊤)) (hs : X.germToFunctionField ⊤ s ≠ 0)

include hs in
theorem ord_eq_zero_iff_mem_basicOpen (x : X) (hx : Order.coheight x = 1) :
    X.ord (X.germToFunctionField ⊤ s) x = 0 ↔ x ∈ X.basicOpen s := by
  have hsn : s ≠ 0 := fun h => hs (by rw [h, map_zero])
  have hgn : X.presheaf.germ ⊤ x (Opens.mem_top _) s ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x (Opens.mem_top _))).mpr hsn
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hgn)
  rw [Thom.Scheme.RegularOrder.Constructions.ord_germToFunctionField X x hx ⊤ (Opens.mem_top _) s hsn,
    Int.natCast_eq_zero, ENat.toNat_eq_zero, or_iff_left hfin,
    Ring.ord, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top, X.mem_basicOpen s x (Opens.mem_top _)]

include hs in
theorem ord_ne_zero_of_not_mem_basicOpen (x : X) (hx : Order.coheight x = 1)
    (hn : x ∉ X.basicOpen s) : X.ord (X.germToFunctionField ⊤ s) x ≠ 0 :=
  fun hz => hn ((ord_eq_zero_iff_mem_basicOpen X s hs x hx).mp hz)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SectionDivisorOrder.Constructions
