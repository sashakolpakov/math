import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ComplexMaps

/-! # Inverse Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.InverseNaturality

noncomputable section

/-! The inverse of the original frame-to-de Rham comparison respects native algebra maps. -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k C D : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [CommRing D] [Algebra k C] [Algebra k D] (f : C →ₐ[k] D)

theorem map : (DeRham.Comparison.frameIso p k C).inv ≫
    ComplexMaps.frameMap p k C D f =
      ComplexMaps.deRhamMap p k C D f ≫ (DeRham.Comparison.frameIso p k D).inv :=
  (DeRham.Comparison.frameIso p k C).inv_comp_eq.mpr
    (((DeRham.Comparison.frameIso p k D).eq_comp_inv.mpr
      (ComplexMaps.naturality p k C D f)).trans (Category.assoc _ _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.InverseNaturality
