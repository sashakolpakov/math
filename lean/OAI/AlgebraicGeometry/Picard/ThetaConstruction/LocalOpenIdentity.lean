import OAI.AlgebraicGeometry.Picard.ThetaConstruction.UnramifiedStalkNeighborhood
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.OpenUnitUnramifiedGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.StalkFlat

/-! # Local Open Identity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalOpenIdentity.Geometric

noncomputable section

/-! Over an actual local-ring spectrum, unramifiedness at the
closed identity makes the whole identity section open. The resulting
group is formally unramified over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem local_section_open_of_unramified_stalk
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    (s : Spec (.of R) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (h : (p.stalkMap (s (IsLocalRing.closedPoint R))).hom.FormallyUnramified) :
    IsOpenImmersion s := by
  obtain ⟨V, hV, hp⟩ := UnramifiedStalkNeighborhood.Geometric.exists_unramified_of_stalk p (s (IsLocalRing.closedPoint R)) h
  let := hp
  have htop : s ⁻¹ᵁ V = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem s hV
  have hrange : Set.range s ⊆ Set.range V.ι := by
    rintro _ ⟨y, rfl⟩
    have hy : s y ∈ V := by
      change y ∈ s ⁻¹ᵁ V
      rw [htop]
      trivial
    exact ⟨⟨s y, hy⟩, rfl⟩
  let t := IsOpenImmersion.lift V.ι s hrange
  have ht : t ≫ V.ι = s := IsOpenImmersion.lift_fac V.ι s hrange
  have ht' : t ≫ (V.ι ≫ p) = 𝟙 _ := (Category.assoc t V.ι p).symm.trans
    ((congrArg (fun z => z ≫ p) ht).trans hs)
  let : IsOpenImmersion t := AbelianModuli.HilbertConstruction.UnramifiedSections.section_isOpenImmersion_of_unramified (V.ι ≫ p) t ht'
  have hi : IsOpenImmersion (t ≫ V.ι) := inferInstance
  exact ht ▸ hi

theorem group_formallyUnramified_of_closed_identity_stalk
    {R : Type u} [CommRing R] [IsLocalRing R]
    (G : Over (Spec (.of R))) [GrpObj G] [LocallyOfFiniteType G.hom]
    (h : (G.hom.stalkMap (η[G].left (IsLocalRing.closedPoint R))).hom.FormallyUnramified) :
    FormallyUnramified G.hom := by
  let : IsOpenImmersion η[G].left :=
    local_section_open_of_unramified_stalk G.hom η[G].left η[G].w h
  exact OpenUnitUnramifiedGroup.Geometric.group_formallyUnramified_of_open_unit G

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalOpenIdentity.Geometric
