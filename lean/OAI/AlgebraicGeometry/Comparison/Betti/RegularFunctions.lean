import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Regular Functions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RegularFunctions

noncomputable section

/-!
# Regular functions as analytic functions on actual complex points

Evaluation is induced by the complex point's actual map on structure-sheaf
sections. Analyticity is tested in the established affine regular-coordinate
charts, allowing varying dimensions. The tests and all maps are concrete;
no cohomological comparison property is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

/-- Evaluate global regular functions through the actual point's section map. -/
def globalEvaluation {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Γ(X.left, ⊤) →ₐ[ℂ] ℂ where
  __ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp p.left.appTop.hom
  commutes' c := by
    have hcomp : X.hom.appTop ≫ p.left.appTop = 𝟙 Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) := by
      calc
        _ = (p.left ≫ X.hom).appTop := rfl
        _ = Scheme.Hom.appTop (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) :=
          congrArg (fun g : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => g.appTop) p.w
        _ = _ := by simp
    have htop : X.hom.appLE ⊤ ⊤ le_top ≫ p.left.appTop = 𝟙 Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) :=
      (congrArg (fun g => g ≫ p.left.appTop)
        (X.hom.app_eq_appLE (U := ⊤))).symm.trans hcomp
    change (Scheme.ΓSpecIso (.of ℂ)).hom
      (p.left.appTop ((X.hom.appLE ⊤ ⊤ le_top)
        ((Scheme.ΓSpecIso (.of ℂ)).inv c))) = c
    have h := ConcreteCategory.congr_hom htop ((Scheme.ΓSpecIso (.of ℂ)).inv c)
    change p.left.appTop ((X.hom.appLE ⊤ ⊤ le_top)
      ((Scheme.ΓSpecIso (.of ℂ)).inv c)) = (Scheme.ΓSpecIso (.of ℂ)).inv c at h
    rw [h]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of ℂ)) c

theorem globalEvaluation_map {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (s : Γ(Y.left, ⊤)) :
    globalEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) s = globalEvaluation p (f.left.appTop s) :=
  rfl

/-- On an affine point, this is the ordinary value of the corresponding character. -/
theorem globalEvaluation_affine (A : CommAlgCat ℂ) (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (s : Γ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left, ⊤)) :
    globalEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A p) s =
      p ((Scheme.ΓSpecIso (CommRingCat.of A)).hom s) := by
  change (Scheme.ΓSpecIso (.of ℂ)).hom ((Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A p).left.appTop s) = _
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left A p]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom p.toRingHom)) s

theorem globalEvaluation_continuous (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤)) :
    Continuous (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => globalEvaluation p s) := by
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineTests _).mpr
  intro A f
  have h : (fun p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A =>
      globalEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f p) s) =
      (fun p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A =>
        p ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (f.left.appTop s))) := by
    funext p
    exact globalEvaluation_affine A p (f.left.appTop s)
  rw [h]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval _

def globalSectionContinuousAlgHom (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Γ(X.left, ⊤) →ₐ[ℂ] C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ℂ) where
  toFun s := ⟨fun p => globalEvaluation p s, globalEvaluation_continuous X s⟩
  map_zero' := by ext p; exact map_zero (globalEvaluation p)
  map_one' := by ext p; exact map_one (globalEvaluation p)
  map_add' s t := by ext p; exact map_add (globalEvaluation p) s t
  map_mul' s t := by ext p; exact map_mul (globalEvaluation p) s t
  commutes' c := by ext p; exact (globalEvaluation p).commutes c

/-- Analyticity in all genuine affine regular-coordinate tests. This is a
condition on actual continuous functions, not an abstract analytic space. -/
def RegularCoordinateAnalytic (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (g : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ℂ)) : Prop :=
  ∀ (A : CommAlgCat ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (n : ℕ)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ)),
    e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n →
      ContDiffOn ℂ ω (fun z => g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f (e.symm z))) e.target

def regularAnalyticFunctions (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Subalgebra ℂ C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ℂ) where
  carrier := {g | RegularCoordinateAnalytic X g}
  zero_mem' := by intro A f n e he; exact contDiffOn_const
  one_mem' := by intro A f n e he; exact contDiffOn_const
  add_mem' := by
    intro g h hg hh A f n e he
    exact (hg A f n e he).add (hh A f n e he)
  mul_mem' := by
    intro g h hg hh A f n e he
    exact (hg A f n e he).mul (hh A f n e he)
  algebraMap_mem' c := by intro A f n e he; exact contDiffOn_const

/-- The affine chart formula proves analytic regularity of actual section evaluation. -/
theorem globalSection_regularAnalytic (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤)) :
    RegularCoordinateAnalytic X (globalSectionContinuousAlgHom X s) := by
  intro A f n e he
  have h : (fun z => (globalSectionContinuousAlgHom X s)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f (e.symm z))) =
      (fun z => e.symm z ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (f.left.appTop s))) := by
    funext z
    exact globalEvaluation_affine A (e.symm z) (f.left.appTop s)
  rw [h]
  exact he.1 _

/-- The canonical analytic realization of global regular functions. -/
def globalSectionAnalyticAlgHom (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Γ(X.left, ⊤) →ₐ[ℂ] regularAnalyticFunctions X :=
  (globalSectionContinuousAlgHom X).codRestrict (regularAnalyticFunctions X)
    (globalSection_regularAnalytic X)

/-- Pullback of analytic functions is literal composition on complex points. -/
def analyticFunctionPullback {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    regularAnalyticFunctions Y →ₐ[ℂ] regularAnalyticFunctions X where
  toFun g :=
    ⟨g.val.comp (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f), by
      intro A i n e he
      change ContDiffOn ℂ ω
        (fun z => g.val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z)))) e.target
      simpa only [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp] using g.property A (i ≫ f) n e he⟩
  map_zero' := by ext p; rfl
  map_one' := by ext p; rfl
  map_add' := by intros; ext p; rfl
  map_mul' := by intros; ext p; rfl
  commutes' := by intro c; ext p; rfl

/-- Algebraic pullback and analytic realization commute on actual regular functions. -/
theorem globalSectionAnalyticAlgHom_naturality {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    (analyticFunctionPullback f).comp (globalSectionAnalyticAlgHom Y) =
      (globalSectionAnalyticAlgHom X).comp (Algebraic.Sheaves.sectionPullback f ⊤) := by
  ext s p
  rfl

theorem analyticFunctionPullback_id (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    analyticFunctionPullback (𝟙 X) = AlgHom.id ℂ (regularAnalyticFunctions X) := by
  ext g p
  change g.val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (𝟙 X) p) = g.val p
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_id]

theorem analyticFunctionPullback_comp {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    analyticFunctionPullback (f ≫ g) = (analyticFunctionPullback f).comp (analyticFunctionPullback g) := by
  ext s p
  change s.val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f ≫ g) p) =
    s.val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp]

end

end OAI.AlgebraicGeometry.Comparison.Betti.RegularFunctions
