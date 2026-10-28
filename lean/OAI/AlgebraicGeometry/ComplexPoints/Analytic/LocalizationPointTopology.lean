import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalizationPointEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PrincipalOpen
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Localization Point Topology -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Localization charts and gluing for ordinary affine complex points

Restriction from a principal localization is a homeomorphism onto the
ordinary open set where the inverted regular function is nonzero. These
charts identify localization at a product with the intersection of the two
corresponding chart images. A unit-ideal family of such charts detects
continuity, giving the topological gluing property for this affine atlas.
-/

universe u v w

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The actual map of complex points induced by the localization algebra map. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction (g : A) :
    C(Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g), Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (Algebra.algHom ℂ A (Localization.Away g))

@[simp] theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction_apply (g : A)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) (a : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g x a = x (algebraMap A (Localization.Away g) a) := rfl

/-- A principal localization is the ordinary open chart on which its denominator
is nonzero, with the genuine complex-point topology on both sides. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph (g : A) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g) ≃ₜ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g where
  toEquiv := Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizationPointEquiv (K := ℂ) g
  continuous_toFun := by
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g).continuous.subtype_mk _
  continuous_invFun := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizationPointEquiv_symm g

@[simp] theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph_val (g : A)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g x).val = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g x := rfl

/-- The image of a localization chart is exactly its principal open set. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.range_localizationRestriction (g : A) :
    Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g y).property
  · intro hx
    refine ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g).apply_symm_apply ⟨x, hx⟩)

/-- The algebraic localization map induces an open embedding of ordinary point spaces. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction (g : A) :
    Topology.IsOpenEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g) := by
  change Topology.IsOpenEmbedding
    ((Subtype.val : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen g → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) ∘ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g)
  exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_principalOpen g).isOpenEmbedding_subtypeVal.comp
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g).isOpenEmbedding

/-- Localization at a product has precisely the overlap of the individual chart images. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localization_chart_overlap (g h : A) :
    Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction (g * h)) =
      Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g) ∩ Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction h) := by
  simp only [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.range_localizationRestriction, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen_mul]

/-- A family generating the unit ideal is an open atlas of localization charts. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.iUnion_range_localizationRestriction {ι : Type v}
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤) :
    (⋃ i, Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction (g i))) = Set.univ := by
  simp only [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.range_localizationRestriction]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.iUnion_principalOpen_eq_univ g hg

/-- Continuity can be checked on the actual principal-localization point spaces.
This is the gluing property of the ordinary affine localization atlas. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff_localizationCover {ι : Type v} {X : Type w} [TopologicalSpace X]
    (g : ι → A) (hg : Ideal.span (Set.range g) = ⊤)
    (F : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → X) :
    Continuous F ↔ ∀ i, Continuous (F ∘ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction (g i)) := by
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff_principalOpen_cover g hg F]
  apply forall_congr'
  intro i
  change Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i) => F x.val) ↔
    Continuous ((fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen (g i) => F x.val) ∘ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph (g i))
  exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph (g i)).comp_continuous_iff'.symm

end

end OAI.AlgebraicGeometry
