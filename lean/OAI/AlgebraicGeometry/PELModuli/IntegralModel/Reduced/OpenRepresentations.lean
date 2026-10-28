import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict

/-! # Open Representations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.OpenRepresentations

noncomputable section

/-! Local representations on reduced tests determine actual comparison
maps on overlaps of their base opens. This is generic atlas bookkeeping. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

structure ReducedOpenRepresentation {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type) (U : S.Opens) where
  space : Over S
  reduced : IsReduced space.left
  mapsTo : ∀ z : space.left, space.hom z ∈ U
  sectionValue : F.obj (op space)
  classifies : ∀ (T : Over S) [IsReduced T.left],
    (∀ t : T.left, T.hom t ∈ U) →
      Function.Bijective (fun f : T ⟶ space => F.map f.op sectionValue)

namespace ReducedOpenRepresentation
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {U V : S.Opens}
    (D : ReducedOpenRepresentation F U) (E : ReducedOpenRepresentation F V)

def homEquiv (T : Over S) [IsReduced T.left] (hT : ∀ t : T.left, T.hom t ∈ U) :
    (T ⟶ D.space) ≃ F.obj (op T) := Equiv.ofBijective _ (D.classifies T hT)

def overlap (D : ReducedOpenRepresentation F U) (_E : ReducedOpenRepresentation F V) :
    Over S := Over.mk ((D.space.hom ⁻¹ᵁ V).ι ≫ D.space.hom)

def inclusion : D.overlap E ⟶ D.space := Over.homMk (D.space.hom ⁻¹ᵁ V).ι rfl

instance inclusion_open : IsOpenImmersion (D.inclusion E).left :=
  inferInstanceAs (IsOpenImmersion (D.space.hom ⁻¹ᵁ V).ι)

instance inclusion_mono : Mono (D.inclusion E) :=
  (Over.forget S).mono_of_mono_map
    (show Mono (D.inclusion E).left from inferInstance)

instance overlap_reduced : IsReduced (D.overlap E).left := by
  have := D.reduced
  exact inferInstanceAs (IsReduced (D.space.hom ⁻¹ᵁ V).toScheme)

theorem overlap_mapsTo_right (z : (D.overlap E).left) : (D.overlap E).hom z ∈ V := z.property

theorem overlap_mapsTo_left (z : (D.overlap E).left) : (D.overlap E).hom z ∈ U := D.mapsTo z.val

def comparisonToSpace : D.overlap E ⟶ E.space :=
  (E.homEquiv (D.overlap E) (D.overlap_mapsTo_right E)).symm
    (F.map (D.inclusion E).op D.sectionValue)

theorem comparisonToSpace_value :
    F.map (D.comparisonToSpace E).op E.sectionValue = F.map (D.inclusion E).op D.sectionValue :=
  (E.homEquiv (D.overlap E) (D.overlap_mapsTo_right E)).apply_symm_apply _

def comparison : D.overlap E ⟶ E.overlap D := by
  let f := D.comparisonToSpace E
  have hr : Set.range f.left ⊆ Set.range (E.space.hom ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change E.space.hom (f.left z) ∈ U
    have h : E.space.hom (f.left z) = (D.overlap E).hom z :=
      congrArg (fun q : (D.overlap E).left ⟶ S => q z) f.w
    rw [h]
    exact D.overlap_mapsTo_left E z
  let b := IsOpenImmersion.lift (E.space.hom ⁻¹ᵁ U).ι f.left hr
  have hb : b ≫ (E.space.hom ⁻¹ᵁ U).ι = f.left := IsOpenImmersion.lift_fac _ _ _
  refine Over.homMk b ?_
  change b ≫ ((E.space.hom ⁻¹ᵁ U).ι ≫ E.space.hom) = _
  rw [← Category.assoc, hb]
  exact f.w

theorem comparison_inclusion : D.comparison E ≫ E.inclusion D = D.comparisonToSpace E := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem comparison_value :
    F.map (D.comparison E).op (F.map (E.inclusion D).op E.sectionValue) =
      F.map (D.inclusion E).op D.sectionValue := by
  calc
    _ = F.map (D.comparison E ≫ E.inclusion D).op E.sectionValue :=
      (F.map_comp_apply (E.inclusion D).op (D.comparison E).op E.sectionValue).symm
    _ = F.map (D.comparisonToSpace E).op E.sectionValue := by rw [comparison_inclusion]
    _ = _ := D.comparisonToSpace_value E

theorem hom_ext {T : Over S} [IsReduced T.left] (f g : T ⟶ D.space)
    (h : F.map f.op D.sectionValue = F.map g.op D.sectionValue) : f = g := by
  apply (D.classifies T (fun t => ?_)).injective h
  have ht := D.mapsTo (f.left t)
  exact (congrArg (fun q : T.left ⟶ S => q t) f.w) ▸ ht

theorem overlap_hom_ext {T : Over S} [IsReduced T.left] (f g : T ⟶ D.overlap E)
    (h : F.map f.op (F.map (D.inclusion E).op D.sectionValue) =
      F.map g.op (F.map (D.inclusion E).op D.sectionValue)) : f = g := by
  apply (cancel_mono (D.inclusion E)).mp
  apply D.hom_ext
  simpa only [op_comp, F.map_comp, types_comp_apply] using h

theorem comparison_comp : D.comparison E ≫ E.comparison D = 𝟙 (D.overlap E) := by
  apply D.overlap_hom_ext E
  simp only [op_comp, F.map_comp, types_comp_apply, op_id, F.map_id, types_id_apply,
    ReducedOpenRepresentation.comparison_value]

def comparisonIso : D.overlap E ≅ E.overlap D where
  hom := D.comparison E
  inv := E.comparison D
  hom_inv_id := D.comparison_comp E
  inv_hom_id := E.comparison_comp D

theorem comparison_self : D.comparison D = 𝟙 (D.overlap D) := by
  apply D.overlap_hom_ext D
  simpa only [op_id, F.map_id, types_id_apply] using D.comparison_value D

end ReducedOpenRepresentation

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.OpenRepresentations
