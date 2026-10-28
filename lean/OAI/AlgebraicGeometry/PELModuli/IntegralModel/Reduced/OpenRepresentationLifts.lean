import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.OpenRepresentations
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Open Representation Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced

noncomputable section

/-! Actual factorization into overlap opens and the diagonal overlap. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {U V : S.Opens}
    (D : OpenRepresentations.ReducedOpenRepresentation F U) (E : OpenRepresentations.ReducedOpenRepresentation F V)

def OpenRepresentations.ReducedOpenRepresentation.overlapLift {T : Over S} (f : T ⟶ D.space) (h : ∀ t : T.left, T.hom t ∈ V) :
    T ⟶ D.overlap E := by
  have hr : Set.range f.left ⊆ Set.range (D.space.hom ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change D.space.hom (f.left t) ∈ V
    have ht : D.space.hom (f.left t) = T.hom t :=
      congrArg (fun q : T.left ⟶ S => q t) f.w
    exact ht ▸ h t
  let b := IsOpenImmersion.lift (D.space.hom ⁻¹ᵁ V).ι f.left hr
  have hb : b ≫ (D.space.hom ⁻¹ᵁ V).ι = f.left := IsOpenImmersion.lift_fac _ _ _
  refine Over.homMk b ?_
  change b ≫ ((D.space.hom ⁻¹ᵁ V).ι ≫ D.space.hom) = _
  rw [← Category.assoc, hb]
  exact f.w

@[reassoc]
theorem OpenRepresentations.ReducedOpenRepresentation.overlapLift_inclusion {T : Over S} (f : T ⟶ D.space)
    (h : ∀ t : T.left, T.hom t ∈ V) : D.overlapLift E f h ≫ D.inclusion E = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

instance OpenRepresentations.ReducedOpenRepresentation.inclusion_self_isIso : IsIso (D.inclusion D) := by
  let f := D.overlapLift D (𝟙 D.space) D.mapsTo
  have hf : f ≫ D.inclusion D = 𝟙 D.space := D.overlapLift_inclusion D _ _
  exact ⟨⟨f, by apply (cancel_mono (D.inclusion D)).mp; simp [hf], hf⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced
