import OAI.Analysis.PDE.Concentration.OuterRegion

namespace OAI.Analysis.PDE.Concentration

open Set Filter
open scoped Topology

theorem cylinderShell_mem_interior {t₀ t₁ a b : ℝ} {x : CylinderSpace}
    (ht : (cylinderComplexEquiv x).1 ∈ Ioo t₀ t₁)
    (hr : ‖(cylinderComplexEquiv x).2‖ ∈ Ioo a b) :
    x ∈ interior (cylinderShell t₀ t₁ a b) := by
  let S : Set CylinderSpace := {y | (cylinderComplexEquiv y).1 ∈ Ioo t₀ t₁ ∧
    ‖(cylinderComplexEquiv y).2‖ ∈ Ioo a b}
  have htime : Continuous (fun y : CylinderSpace => (cylinderComplexEquiv y).1) := by
    simp only [cylinderComplexEquiv_apply]
    fun_prop
  have hS : IsOpen S := (isOpen_Ioo.preimage htime).inter
    (isOpen_Ioo.preimage continuous_cylinderComplexCoordinate.norm)
  have hsub : S ⊆ cylinderShell t₀ t₁ a b := fun y hy =>
    ⟨Ioo_subset_Icc_self hy.1, Ioo_subset_Icc_self hy.2⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hS.mem_nhds ⟨ht, hr⟩) hsub)

theorem cylinderShell_boundary {t₀ t₁ a b : ℝ} {x : CylinderSpace}
    (hx : x ∈ cylinderShell t₀ t₁ a b) (hi : x ∉ interior (cylinderShell t₀ t₁ a b)) :
    (cylinderComplexEquiv x).1 = t₀ ∨ (cylinderComplexEquiv x).1 = t₁ ∨
      ‖(cylinderComplexEquiv x).2‖ = a ∨ ‖(cylinderComplexEquiv x).2‖ = b := by
  by_cases h0 : (cylinderComplexEquiv x).1 = t₀
  · exact Or.inl h0
  by_cases h1 : (cylinderComplexEquiv x).1 = t₁
  · exact Or.inr (Or.inl h1)
  by_cases h2 : ‖(cylinderComplexEquiv x).2‖ = a
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : ‖(cylinderComplexEquiv x).2‖ = b
  · exact Or.inr (Or.inr (Or.inr h3))
  exact False.elim (hi (cylinderShell_mem_interior
    ⟨lt_of_le_of_ne hx.1.1 (fun h => h0 h.symm), lt_of_le_of_ne hx.1.2 h1⟩
    ⟨lt_of_le_of_ne hx.2.1 (fun h => h2 h.symm), lt_of_le_of_ne hx.2.2 h3⟩))

end OAI.Analysis.PDE.Concentration
