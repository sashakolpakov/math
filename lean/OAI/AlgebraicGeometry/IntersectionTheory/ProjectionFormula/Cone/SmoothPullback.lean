import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Generic
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentSmooth
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SupportOpen

/-! # Smooth Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.SmoothPullback

noncomputable section

/-! Pulling the smooth open of the cone's base back through the
ambient projection gives a smooth scheme immersed in the cone. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
  (hL : LinearIndependent ℂ L) (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m)

def baseSupport : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace m) := irreducibleSetEquivPoints.symm η

abbrev baseOpen : Scheme := Smooth.SupportOpen.space (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) (baseSupport η)

abbrev baseInclusion : baseOpen η ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  Smooth.SupportOpen.inclusion (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) (baseSupport η)

abbrev space : Scheme := pullback (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) (baseInclusion η)

def inclusion : space L η ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n :=
  pullback.fst (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) (baseInclusion η) ≫ (Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)).ι

instance immersion : IsImmersion (inclusion L η) := by
  unfold inclusion
  infer_instance

instance noetherian : NoetherianSpace (space L η) :=
  (inclusion L η).isEmbedding.isInducing.noetherianSpace

def base : space L η ⟶ Foundations.Scheme.ProjectiveSpace.complexBase := pullback.snd (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) (baseInclusion η) ≫
  Smooth.SupportOpen.base (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) (baseSupport η)

include hL in
theorem relativeDimension : SmoothOfRelativeDimension
    ((n - m) + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (baseSupport η) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (base L η) := by
  let : SmoothOfRelativeDimension (n - m) (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) := IndependentSmooth.Projection.smooth L hL
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (n - m)) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n - m)
  let : SmoothOfRelativeDimension (n - m) (pullback.snd (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) (baseInclusion η)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension (n - m)) _ _ inferInstance
  unfold base
  infer_instance

theorem over_base : inclusion L η ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = base L η := by
  unfold inclusion base
  rw [Category.assoc, ← Projective.BasicOpen.RationalProjection.over_base (Projective.ConeSupport.coordinates L)
    (HomogeneousCoordinateMap.ofForms_C _ _), pullback.condition_assoc,
    Smooth.SupportOpen.over_base]

include hL in
theorem range_subset : Set.range (inclusion L η) ⊆ (Projective.ConeSupport.support L hL η : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := by
  rintro _ ⟨z, rfl⟩
  apply (Generic.Projection.mem_cone_iff L hL η (pullback.fst (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) (baseInclusion η) z)).mpr
  have he := congrArg (fun f : space L η ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m => f z)
    (pullback.condition (f := Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) (g := baseInclusion η))
  have hm := Smooth.SupportOpen.range_subset (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) (baseSupport η)
    (Set.mem_range_self (pullback.snd (Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) (baseInclusion η) z))
  exact he.symm ▸ hm

include hL in
theorem generic_in_range : Projective.ConeSupport.genericPoint L hL η ∈ Set.range (inclusion L η) := by
  have hη : η ∈ Set.range (baseInclusion η) := by
    have he : CycleClass.Thom.IntersectionGeometry.supportPoint (baseSupport η) = η := irreducibleSetEquivPoints.apply_symm_apply η
    exact Eq.mp (congrArg (fun y : Foundations.Scheme.ProjectiveSpace.projectiveSpace m => y ∈ Set.range (baseInclusion η)) he)
      (Smooth.SupportOpen.generic_in_range (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) (baseSupport η))
  obtain ⟨u, hu⟩ := hη
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Projective.BasicOpen.RationalProjection.map (Projective.ConeSupport.coordinates L)) (g := baseInclusion η) (Generic.Projection.point L hL η) u
    ((Generic.Projection.map_point L hL η).trans hu.symm)
  refine ⟨z, ?_⟩
  exact congrArg (fun y : Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L) => y.val) hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.SmoothPullback
