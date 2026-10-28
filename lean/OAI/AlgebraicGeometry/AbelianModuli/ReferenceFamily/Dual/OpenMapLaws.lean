import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenChart

/-! # Open Map Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenMapLaws

noncomputable section

/-! Literal open subfamilies and their inclusions form a diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [CommRing k] (X : Over (Spec (.of (DualNumber k))))

theorem dualFamilyOpenMap_id (V : X.left.Opens) :
    OpenChart.dualFamilyOpenMap k X (le_refl V) = 𝟙 (OpenChart.dualFamilyOpenObject k X V) := by
  have := OpenChart.dualFamilyOpenInclusion_open k X V
  have : Mono (OpenChart.dualFamilyOpenInclusion k X V) := Over.mono_of_mono_left (OpenChart.dualFamilyOpenInclusion k X V)
  apply (cancel_mono (OpenChart.dualFamilyOpenInclusion k X V)).mp
  rw [OpenChart.dualFamilyOpenMap_inclusion, Category.id_comp]

theorem dualFamilyOpenMap_comp {U V W : X.left.Opens} (h : U ≤ V) (j : V ≤ W) :
    OpenChart.dualFamilyOpenMap k X h ≫ OpenChart.dualFamilyOpenMap k X j = OpenChart.dualFamilyOpenMap k X (h.trans j) := by
  have := OpenChart.dualFamilyOpenInclusion_open k X W
  have : Mono (OpenChart.dualFamilyOpenInclusion k X W) := Over.mono_of_mono_left (OpenChart.dualFamilyOpenInclusion k X W)
  apply (cancel_mono (OpenChart.dualFamilyOpenInclusion k X W)).mp
  rw [Category.assoc, OpenChart.dualFamilyOpenMap_inclusion, OpenChart.dualFamilyOpenMap_inclusion, OpenChart.dualFamilyOpenMap_inclusion]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenMapLaws
