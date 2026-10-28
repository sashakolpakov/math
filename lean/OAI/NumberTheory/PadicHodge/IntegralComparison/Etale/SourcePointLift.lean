import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourceLiftReduction

/-! # Source Point Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourcePointLift

noncomputable section

/-! A point of the original etale source lifts uniquely above a
specified thickened target point. The original residue scheme may be
any nonempty one-point scheme. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X₀ X Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (f : Y₀ ⟶ X₀) [Etale f] [IsAffineHom f]

theorem existsUnique_point_lift {T₀ T : Scheme.{u}} [Nonempty T₀] [Subsingleton T₀]
    (j : T₀ ⟶ T) [IsClosedImmersion j] [Surjective j] (hj : IsNilpotent j.ker)
    (a : T₀ ⟶ Y₀) (b : T ⟶ X) (hab : a ≫ f ≫ i = j ≫ b) :
    ∃! l : T ⟶ SourceLift.source i hi f,
      j ≫ l = a ≫ SourceLift.reduction i hi f ∧ l ≫ SourceLift.map i hi f = b := by
  obtain ⟨c, z, hz⟩ := LiftCharts.sourceMap_covers i f (a (Classical.arbitrary T₀))
  let D := SourceLift.localChart i hi f c
  have hr : Set.range a ⊆ Set.range D.source := by
    rintro _ ⟨t, rfl⟩
    refine ⟨z, ?_⟩
    exact hz.trans (congrArg a (Subsingleton.elim _ t))
  let a₀ := IsOpenImmersion.lift D.source a hr
  have ha₀ : a₀ ≫ D.source = a := IsOpenImmersion.lift_fac _ _ _
  have h : (a₀ ≫ D.reduction) ≫ D.map ≫ D.baseMap = j ≫ b := by
    rw [Category.assoc, D.over, ← Category.assoc a₀ D.source, ha₀]
    exact hab
  obtain ⟨l, hl, _⟩ := AffineOpenNilLift.existsUnique_lift D.map D.baseMap j hj
    (a₀ ≫ D.reduction) b h
  let v := LiftGluedMap.Overlap.chartMap (SourceLift.localChart i hi f) c
  have hv : v ≫ SourceLift.map i hi f = D.toBase := LiftGluedMap.Overlap.chartMap_map _ c
  have hjl : j ≫ (l ≫ v) = a ≫ SourceLift.reduction i hi f := by
    rw [← Category.assoc, hl.1, Category.assoc]
    have hs := LiftGluedMap.Overlap.source_reduction (SourceLift.localChart i hi f)
      (LiftCharts.sourceMap_covers i f) c
    change D.source ≫ SourceLift.reduction i hi f = D.reduction ≫ v at hs
    rw [← hs, ← Category.assoc, ha₀]
  have hbl : (l ≫ v) ≫ SourceLift.map i hi f = b := by rw [Category.assoc, hv]; exact hl.2
  refine ⟨l ≫ v, ⟨hjl, hbl⟩, ?_⟩
  intro m hm
  exact FormallyUnramified.hom_ext j hj (SourceLift.map i hi f) (hm.1.trans hjl.symm) (hm.2.trans hbl.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourcePointLift
