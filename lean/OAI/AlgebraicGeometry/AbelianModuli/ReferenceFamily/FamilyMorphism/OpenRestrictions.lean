import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenDiagram

/-! # Open Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.OpenRestrictions

noncomputable section

/-! A family morphism restricts to every pair of original opens whose
image condition holds. These actual restrictions commute on smaller
opens, without a choice of affine coordinates or a product structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme} {X Y : Over S} (f : X ⟶ Y)

def familyMorphismOpenRestriction (V : X.left.Opens) (W : Y.left.Opens)
    (h : V ≤ f.left ⁻¹ᵁ W) : HilbertConstruction.Open.ParameterPoints.openParameterScheme X V ⟶ HilbertConstruction.Open.ParameterPoints.openParameterScheme Y W :=
  Over.homMk (f.left.resLE W V h) (by
    change f.left.resLE W V h ≫ (W.ι ≫ Y.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, f.w])

theorem familyMorphismOpenRestriction_inclusion (V : X.left.Opens) (W : Y.left.Opens)
    (h : V ≤ f.left ⁻¹ᵁ W) :
    familyMorphismOpenRestriction f V W h ≫ HilbertConstruction.Open.ParameterPoints.openParameterInclusion Y W =
      HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V ≫ f := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι _ _

theorem familyMorphismOpenRestriction_square {V V' : X.left.Opens} {W W' : Y.left.Opens}
    (t : V' ≤ V) (j : W' ≤ W) (h : V ≤ f.left ⁻¹ᵁ W) (h' : V' ≤ f.left ⁻¹ᵁ W') :
    Affine.OpenDiagram.familyOpenMap X t ≫ familyMorphismOpenRestriction f V W h =
      familyMorphismOpenRestriction f V' W' h' ≫ Affine.OpenDiagram.familyOpenMap Y j := by
  have : Mono (HilbertConstruction.Open.ParameterPoints.openParameterInclusion Y W) :=
    Over.mono_of_mono_left (HilbertConstruction.Open.ParameterPoints.openParameterInclusion Y W)
  apply (cancel_mono (HilbertConstruction.Open.ParameterPoints.openParameterInclusion Y W)).mp
  rw [Category.assoc, familyMorphismOpenRestriction_inclusion, ← Category.assoc,
    Affine.OpenDiagram.familyOpenMap_inclusion, Category.assoc, Affine.OpenDiagram.familyOpenMap_inclusion,
    familyMorphismOpenRestriction_inclusion]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.OpenRestrictions
