import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.StalkSections
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange

/-! # Stalk Tail Section -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.StalkTailSection.Constructions

noncomputable section

/-! An element of the ideal of tail germs is represented, on a smaller
open, by an element of the actual tail section ideal. Consequently an
elementary head change can be made before taking germs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped BigOperators

open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.StalkSections.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange.Constructions

universe u
variable (X : Scheme.{u}) (x : X) (B : X.Opens) (hxB : x ∈ B)

theorem exists_tail_section (rs : List Γ(X, B)) (t : X.presheaf.stalk x)
    (ht : t ∈ Ideal.ofList (rs.map (X.presheaf.germ B x hxB))) :
    ∃ C : X.Opens, ∃ hCB : C ≤ B, ∃ hxC : x ∈ C, ∃ u : Γ(X, C),
      u ∈ Ideal.ofList (rs.map (X.presheaf.map (homOfLE hCB).op)) ∧
        X.presheaf.germ C x hxC u = t := by
  classical
  have hspan : Ideal.ofList (rs.map (X.presheaf.germ B x hxB)) =
      Ideal.span (Set.range (fun i : Fin rs.length => X.presheaf.germ B x hxB (rs.get i))) := by
    apply congrArg Ideal.span
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, hy⟩ := List.mem_map.mp hy
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      exact ⟨i, hy⟩
    · rintro ⟨i, rfl⟩
      exact List.mem_map.mpr ⟨rs.get i, List.get_mem rs i, rfl⟩
  rw [hspan] at ht
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ht
  obtain ⟨C, hCB, hxC, a, ha⟩ := Finite.StalkSections.Constructions.exists_finite_sections X x B hxB c
  let ρ := X.presheaf.map (homOfLE hCB).op
  let u : Γ(X, C) := ∑ i, a i * ρ (rs.get i)
  refine ⟨C, hCB, hxC, u, ?_, ?_⟩
  · apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ (a i)
      (Ideal.subset_span (List.mem_map.mpr ⟨rs.get i, List.get_mem rs i, rfl⟩))
  · change X.presheaf.germ C x hxC (∑ i, a i * ρ (rs.get i)) = t
    simp only [map_sum, map_mul, ha]
    exact (Finset.sum_congr rfl (fun i _ => congrArg (fun z => c i * z)
      (X.presheaf.germ_res_apply (homOfLE hCB) x hxC (rs.get i)))).trans hc

theorem exists_head_adjustment (r : Γ(X, B)) (rs : List Γ(X, B)) (t : X.presheaf.stalk x)
    (ht : t ∈ Ideal.ofList (rs.map (X.presheaf.germ B x hxB))) :
    ∃ C : X.Opens, ∃ hCB : C ≤ B, ∃ hxC : x ∈ C, ∃ s : Γ(X, C),
      Ideal.ofList (s :: rs.map (X.presheaf.map (homOfLE hCB).op)) =
        Ideal.ofList ((r :: rs).map (X.presheaf.map (homOfLE hCB).op)) ∧
      X.presheaf.germ C x hxC s = X.presheaf.germ B x hxB r + t := by
  obtain ⟨C, hCB, hxC, u, hu, hgu⟩ := exists_tail_section X x B hxB rs t ht
  let ρ := X.presheaf.map (homOfLE hCB).op
  refine ⟨C, hCB, hxC, ρ r + u, Regular.SequenceTailChange.Constructions.ofList_add_tail (ρ r) u (rs.map ρ) hu, ?_⟩
  rw [map_add, hgu]
  exact congrArg (fun z => z + t) (X.presheaf.germ_res_apply (homOfLE hCB) x hxC r)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.StalkTailSection.Constructions
