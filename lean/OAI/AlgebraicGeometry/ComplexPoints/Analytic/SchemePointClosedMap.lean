import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Scheme Point Closed Map -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

section

/-!
# Actual pullbacks and images of complex scheme points

The ordinary scheme pullback is equipped with its complex structure map. Its
universal property gives the precise point-set identity needed to test images
under a morphism against affine test spaces.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y Z T : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The ordinary scheme fiber product, regarded as a scheme over the same complex base. -/
def SchemePointHomeomorphs.schemeComplexPoints.pullbackOver (f : X ⟶ Z) (g : Y ⟶ Z) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (pullback.snd f.left g.left ≫ Y.hom)

/-- The left projection of the actual fiber product over the complex base. -/
def SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft (f : X ⟶ Z) (g : Y ⟶ Z) : SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f g ⟶ X :=
  Over.homMk (pullback.fst f.left g.left) (by
    change pullback.fst f.left g.left ≫ X.hom = pullback.snd f.left g.left ≫ Y.hom
    calc
      _ = (pullback.fst f.left g.left ≫ f.left) ≫ Z.hom := by
        rw [Category.assoc, Over.w f]
      _ = (pullback.snd f.left g.left ≫ g.left) ≫ Z.hom := by
        rw [pullback.condition]
      _ = _ := by rw [Category.assoc, Over.w g])

/-- The right projection of the actual fiber product over the complex base. -/
def SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight (f : X ⟶ Z) (g : Y ⟶ Z) : SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f g ⟶ Y :=
  Over.homMk (pullback.snd f.left g.left) (by rfl)

/-- The two projections satisfy the actual scheme pullback relation. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.pullback_condition (f : X ⟶ Z) (g : Y ⟶ Z) :
    SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g ≫ f = SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g ≫ g := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- Compatible morphisms over the complex base lift to the actual fiber product. -/
def SchemePointHomeomorphs.schemeComplexPoints.pullbackLift (f : X ⟶ Z) (g : Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y)
    (h : x ≫ f = y ≫ g) : T ⟶ SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f g :=
  Over.homMk
    (pullback.lift x.left y.left (congrArg (fun q : T ⟶ Z => q.left) h)) (by
      change (pullback.lift x.left y.left _) ≫
        (pullback.snd f.left g.left ≫ Y.hom) = T.hom
      rw [← Category.assoc, pullback.lift_snd, Over.w y])

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toLeft (f : X ⟶ Z) (g : Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y)
    (h : x ≫ f = y ≫ g) :
    SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g x y h ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g = x := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toRight (f : X ⟶ Z) (g : Y ⟶ Z) (x : T ⟶ X) (y : T ⟶ Y)
    (h : x ≫ f = y ≫ g) :
    SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g x y h ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g = y := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- Pulling an image back along a test map is the image from the actual fiber product. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.preimage_image_eq_pullback_image (f : X ⟶ Z) (g : Y ⟶ Z)
    (s : Set (SchemePointHomeomorphs.schemeComplexPoints X)) :
    SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (SchemePointHomeomorphs.schemeComplexPoints.map f '' s) =
      SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g) '' (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) ⁻¹' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g x y hxy, ?_, ?_⟩
    · change (SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g x y hxy ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) ∈ s
      exact (SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toLeft f g x y hxy).symm ▸ hx
    · exact SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toRight f g x y hxy
  · rintro ⟨p, hp, rfl⟩
    refine ⟨SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) p, hp, ?_⟩
    change (p ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) ≫ f = (p ≫ SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g) ≫ g
    simpa only [Category.assoc] using
      congrArg (fun q => p ≫ q) (SchemePointHomeomorphs.schemeComplexPoints.pullback_condition f g)

end

/-!
# Closed maps tested on actual affine pullbacks

This module establishes the topological descent step for closed immersions.
Its local premise is an ordinary closed-map assertion on each actual affine
pullback; the closed-immersion module proves that premise from the algebraic
closed-immersion property.
-/

open _root_.CategoryTheory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Closedness in the affine-test topology is checked on the actual affine test maps. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosed_iff_affineTests (s : Set (SchemePointHomeomorphs.schemeComplexPoints X)) :
    IsClosed s ↔ ∀ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X),
      IsClosed (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f ⁻¹' s) := by
  constructor
  · intro hs A f
    exact hs.preimage (SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A f)
  · intro hs
    rw [← isOpen_compl_iff]
    apply (SchemePointHomeomorphs.schemeComplexPoints.isOpen_iff_affineTests _).mpr
    intro A f
    exact (hs A f).isOpen_compl

/-- Closedness of all affine pullback point maps implies closedness of the global point map. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosedMap_map_of_affine_pullbacks (f : X ⟶ Y)
    (h : ∀ (A : CommAlgCat ℂ) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y),
      IsClosedMap (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g))) :
    IsClosedMap (SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro s hs
  apply (SchemePointHomeomorphs.schemeComplexPoints.isClosed_iff_affineTests _).mpr
  intro A g
  have hclosed : IsClosed
      (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g) '' (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g) ⁻¹' s)) :=
    h A g _ (hs.preimage (SchemePointHomeomorphs.schemeComplexPoints.continuous_map (SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g)))
  change IsClosed ((SchemePointHomeomorphs.affineSchemePointEquiv A) ⁻¹' (SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (SchemePointHomeomorphs.schemeComplexPoints.map f '' s)))
  rw [SchemePointHomeomorphs.schemeComplexPoints.preimage_image_eq_pullback_image f g s]
  exact hclosed.preimage (SchemePointHomeomorphs.affineSchemePointHomeomorph A).continuous

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
