import OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm

/-! # Stalk Sections -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.StalkSections.Constructions

noncomputable section

/-! Finitely many actual stalk elements admit simultaneous regular
section representatives on an arbitrarily small scheme neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v
variable (X : Scheme.{u}) (x : X) (B : X.Opens) (hxB : x ∈ B)

include hxB in
theorem exists_finite_sections {ι : Type v} [Finite ι] (r : ι → X.presheaf.stalk x) :
    ∃ C ≤ B, ∃ hxC : x ∈ C, ∃ s : ι → Γ(X, C), ∀ i, X.presheaf.germ C x hxC (s i) = r i := by
  classical
  choose U hUB hxU t ht using fun i : ι => X.presheaf.exists_le_germ_eq (r i) hxB
  let C : X.Opens := B ⊓ iInf U
  have hCU (i : ι) : C ≤ U i := inf_le_right.trans (iInf_le U i)
  have hxC : x ∈ C := by
    refine ⟨hxB, ?_⟩
    change x ∈ ((iInf U : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxU
  refine ⟨C, inf_le_left, hxC, fun i => X.presheaf.map (homOfLE (hCU i)).op (t i), ?_⟩
  intro i
  exact (X.presheaf.germ_res_apply (homOfLE (hCU i)) x hxC (t i)).trans (ht i)

include hxB in
theorem exists_section_list (rs : List (X.presheaf.stalk x)) :
    ∃ C ≤ B, ∃ hxC : x ∈ C, ∃ ss : List Γ(X, C), ss.map (X.presheaf.germ C x hxC) = rs := by
  obtain ⟨C, hCB, hxC, s, hs⟩ := exists_finite_sections X x B hxB (fun i : Fin rs.length => rs.get i)
  refine ⟨C, hCB, hxC, List.ofFn s, ?_⟩
  rw [List.map_ofFn]
  exact (congrArg List.ofFn (funext hs)).trans (List.ofFn_get rs)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.StalkSections.Constructions
