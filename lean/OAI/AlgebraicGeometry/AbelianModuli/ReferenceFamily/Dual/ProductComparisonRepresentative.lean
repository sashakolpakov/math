import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct

/-! # Product Comparison Representative -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductComparisonRepresentative

noncomputable section

/-! A representative proved equal to the canonical fiber comparison.
The equality retains the original comparison while avoiding repeated
expansion of the adjunction construction in dependent proof types. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

private theorem exists_equal_comparison {A : Sort*} (a : A) : ∃ b : A, b = a := ⟨a, rfl⟩

def dualProductComparisonRepresentative (k : Type) [CommRing k] :=
  Classical.choose (exists_equal_comparison (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k))

theorem dualProductComparisonRepresentative_eq (k : Type) [CommRing k] :
    dualProductComparisonRepresentative k = Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k :=
  Classical.choose_spec (exists_equal_comparison (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProductComparisonRepresentative
