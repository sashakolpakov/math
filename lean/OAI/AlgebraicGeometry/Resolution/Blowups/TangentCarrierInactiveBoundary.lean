import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierBoundaryReindex
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruencePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.RefinementNeighborhood

/-! # Tangent Carrier Inactive Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Boundary components absent from a point impose no extra restriction after an actual common open refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt.exists_with_inactive_boundary
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J H H' : X.IdealSheafData}
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (F : Finset β) {n : ℕ} {x : X}
    (A : TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt f J H H' (fun i : F => D i.val) n x)
    (hx : x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support)
    (hF : ∀ i, i ∉ F → x ∉ (D i).support) : Nonempty (TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt f J H H' D n x) := by
  classical
  have hp : A.point ∈ ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap A.left).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change A.left A.point ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support
    rwa [A.point_eq]
  have hright : A.right A.point = x :=
    (A.congruence.point_eq_on_support A.point hp).symm.trans A.point_eq
  let E : Bool × β → A.ambient.IdealSheafData := fun i =>
    if i.1 then (D i.2).comap A.left else (D i.2).comap A.right
  let W := Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood E A.point
  have hpW : A.point ∈ W := Boundary.RefinementNeighborhood.Construction.mem_boundaryRefinementNeighborhood E A.point
  have hunit (i : β) (hi : i ∉ F) :
      ((D i).comap A.left).comap W.ι = ⊤ ∧ ((D i).comap A.right).comap W.ι = ⊤ := by
    have hl : A.point ∉ ((D i).comap A.left).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change A.left A.point ∉ (D i).support
      rw [A.point_eq]
      exact hF i hi
    have hr : A.point ∉ ((D i).comap A.right).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change A.right A.point ∉ (D i).support
      rw [hright]
      exact hF i hi
    exact ⟨Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood_unit E A.point (true, i) hl,
      Boundary.RefinementNeighborhood.Construction.boundaryRefinementNeighborhood_unit E A.point (false, i) hr⟩
  refine ⟨{ ambient := W.toScheme
            left := W.ι ≫ A.left
            right := W.ι ≫ A.right
            left_etale := inferInstance
            right_etale := inferInstance
            ground := ?_
            ideal := ?_
            carrier := ?_
            boundary := ?_
            congruence := A.congruence.comp W.ι
            point := ⟨A.point, hpW⟩
            point_eq := A.point_eq }⟩
  · rw [Category.assoc, Category.assoc, A.ground]
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, A.ideal]
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, A.carrier]
  · intro i
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    by_cases hi : i ∈ F
    · rw [A.boundary ⟨i, hi⟩]
    · exact (hunit i hi).1.trans (hunit i hi).2.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
