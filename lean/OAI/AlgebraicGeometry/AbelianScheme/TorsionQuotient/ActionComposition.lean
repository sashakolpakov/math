import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FreeConstant

/-! # Action Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ActionComposition.FreeConstantAction

/-! Composition and the full equivalence relation of a free constant action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X : Over S} {G : Type u} [Group G] (d : FreeConstant.FreeConstantAction.Data X G)

noncomputable def label {T : Over S} (f : T ⟶ FreeConstant.FreeConstantAction.relation (X := X) (G := G)) :
    LocallyConstant T.left G := ConstantPointsIs.ConstantPoints.index f.left

omit [Group G] in
theorem label_comp_inclusion {T : Over S} (a : T ⟶ X) (g : G) :
    label (a ≫ FreeConstant.FreeConstantAction.inclusion g) = LocallyConstant.const T.left g :=
  ConstantPointsIs.ConstantPoints.index_ι_comp a.left g

noncomputable def compositionLabels :
    LocallyConstant (pullback (FreeConstant.FreeConstantAction.target d) (FreeConstant.FreeConstantAction.source (G := G))).left G :=
  label (pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) * label (pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source)

noncomputable def composition : pullback (FreeConstant.FreeConstantAction.target d) (FreeConstant.FreeConstantAction.source (G := G)) ⟶
    FreeConstant.FreeConstantAction.relation (X := X) (G := G) :=
  Over.homMk
    (ConstantPointsIs.ConstantPoints.lift ((pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source ≫ FreeConstant.FreeConstantAction.source).left) (compositionLabels d)) (by
      change ConstantPointsIs.ConstantPoints.lift _ _ ≫ ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X.left G).hom ≫ X.hom) = _
      rw [← Category.assoc, ConstantPointsIs.ConstantPoints.lift_base]
      exact (pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source ≫ FreeConstant.FreeConstantAction.source).w)

theorem composition_source : composition d ≫ FreeConstant.FreeConstantAction.source = pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source ≫ FreeConstant.FreeConstantAction.source :=
  Over.OverMorphism.ext (ConstantPointsIs.ConstantPoints.lift_base _ _)

theorem composition_label : label (composition d) = compositionLabels d :=
  ConstantPointsIs.ConstantPoints.index_lift _ _

omit [Group G] in
theorem label_of_factor {T : Over S} (f : T ⟶ FreeConstant.FreeConstantAction.relation (X := X) (G := G)) (g : G)
    (h : f = (f ≫ FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.inclusion g) :
    label f = LocallyConstant.const T.left g :=
  (congrArg label h).trans (label_comp_inclusion _ _)

theorem composition_target [Etale X.hom] :
    composition d ≫ FreeConstant.FreeConstantAction.target d = pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source ≫ FreeConstant.FreeConstantAction.target d := by
  apply IsogenyQuotient.EtaleDetection.Construction.etale_ext_of_field_points
  intro K hK s z
  obtain ⟨g, hg⟩ := FreeConstant.FreeConstantAction.field_factor K s (z ≫ pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source)
  obtain ⟨h, hh⟩ := FreeConstant.FreeConstantAction.field_factor K s (z ≫ pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source)
  obtain ⟨k, hk⟩ := FreeConstant.FreeConstantAction.field_factor K s (z ≫ composition d)
  let z₀ : Spec (CommRingCat.of K) := default
  have hg' := congrArg (fun c => c z₀) (label_of_factor _ g hg)
  have hh' := congrArg (fun c => c z₀) (label_of_factor _ h hh)
  have hk' := congrArg (fun c => c z₀) (label_of_factor _ k hk)
  have hp : label (z ≫ composition d) z₀ =
      label (z ≫ pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) z₀ *
        label (z ≫ pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) z₀ :=
    congrArg (fun c => c (z.left z₀)) (composition_label d)
  have hkg : k = g * h := hk'.symm.trans (hp.trans (congrArg₂ (· * ·) hg' hh'))
  have hb : (z ≫ pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.target d =
      (z ≫ pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.source := by
    simpa only [Category.assoc] using
      congrArg (fun f => z ≫ f) (pullback.condition (f := FreeConstant.FreeConstantAction.target d) (g := FreeConstant.FreeConstantAction.source))
  have hfirst : ((z ≫ pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.source) ≫ d.map g =
      (z ≫ pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.source := by
    apply Eq.trans _ hb
    simpa only [Category.assoc, FreeConstant.FreeConstantAction.inclusion_target] using
      (congrArg (fun f => f ≫ FreeConstant.FreeConstantAction.target d) hg).symm
  have hlast : ((z ≫ pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.source) ≫ d.map h =
      (z ≫ pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.target d := by
    simpa only [Category.assoc, FreeConstant.FreeConstantAction.inclusion_target] using
      (congrArg (fun f => f ≫ FreeConstant.FreeConstantAction.target d) hh).symm
  calc
    z ≫ composition d ≫ FreeConstant.FreeConstantAction.target d = ((z ≫ composition d) ≫ FreeConstant.FreeConstantAction.source) ≫ d.map k := by
      simpa only [Category.assoc, FreeConstant.FreeConstantAction.inclusion_target] using
        congrArg (fun f => f ≫ FreeConstant.FreeConstantAction.target d) hk
    _ = ((z ≫ pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.source) ≫ d.map (g * h) := by
      rw [hkg]
      exact congrArg (fun f => f ≫ d.map (g * h)) (by
        simpa only [Category.assoc] using congrArg (fun f => z ≫ f) (composition_source d))
    _ = (((z ≫ pullback.fst (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source) ≫ FreeConstant.FreeConstantAction.source) ≫ d.map g) ≫ d.map h := by
      rw [← d.map_mul]
      simp only [Category.assoc]
    _ = z ≫ pullback.snd (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source ≫ FreeConstant.FreeConstantAction.target d := by
      rw [hfirst, hlast, Category.assoc]

noncomputable def equivalenceRelation [Etale X.hom] :
    CategoryTheory.EquivalenceRelation (FreeConstant.FreeConstantAction.source (X := X) (G := G)) (FreeConstant.FreeConstantAction.target d) where
  right_cancellation := (FreeConstant.FreeConstantAction.jointly_monic d).right_cancellation
  r := FreeConstant.FreeConstantAction.inclusion 1
  reflexivity₁ := FreeConstant.FreeConstantAction.inclusion_source 1
  reflexivity₂ := (FreeConstant.FreeConstantAction.inclusion_target d 1).trans d.map_one
  s := FreeConstant.FreeConstantAction.symmetry d
  symmetry₁ := FreeConstant.FreeConstantAction.symmetry_source d
  symmetry₂ := FreeConstant.FreeConstantAction.symmetry_target d
  c := pullback.cone (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source
  isLimit := pullback.isLimit (FreeConstant.FreeConstantAction.target d) FreeConstant.FreeConstantAction.source
  t := composition d
  transitivity₁ := composition_source d
  transitivity₂ := composition_target d

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ActionComposition.FreeConstantAction
