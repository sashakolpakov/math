import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts

/-! # Family Translations -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FamilyTranslations.Abelian.FamilyPoints

noncomputable section

/-!
Translation by an actual algebraic section is a continuous map of the
total native family. Its action on each literal fiber is the given group
translation, through the actual base-change point equivalence.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Topology

variable {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)

def sectionBasePoint (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    (Over.map s.left).obj (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ⟶ Over.mk (𝟙 S.left) :=
  Over.homMk s.left (by simp)

def fiberSection (t : Over.mk (𝟙 S.left) ⟶ G.scheme) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme :=
  (G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))).symm
    (sectionBasePoint S s ≫ t)

def familySection (t : Over.mk (𝟙 S.left) ⟶ G.scheme) : S ⟶ AbelianFamilyPoints.FamilyPoints.total S G :=
  Over.homMk t.left (by
    change t.left ≫ (G.scheme.hom ≫ S.hom) = S.hom
    rw [← Category.assoc, t.w]
    exact Category.id_comp _)

theorem fiberSection_inclusion (t : Over.mk (𝟙 S.left) ⟶ G.scheme)
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (fiberSection S G t s) =
      s ≫ familySection S G t := by
  let e := G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
  apply Over.OverMorphism.ext
  exact congrArg
    (fun w : G.Points ((Over.map s.left).obj (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) => w.left)
    (e.apply_symm_apply (sectionBasePoint S s ≫ t))

theorem fiberSection_continuous (t : Over.mk (𝟙 S.left) ⟶ G.scheme) :
    Continuous (fun s => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (fiberSection S G t s)) := by
  have he : (fun s => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (fiberSection S G t s)) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (familySection S G t) :=
    funext (fiberSection_inclusion S G t)
  rw [he]
  exact AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _

def translationEndomorphism (t : Over.mk (𝟙 S.left) ⟶ G.scheme) :
    G.scheme ⟶ G.scheme :=
  ((Over.homMk G.scheme.hom (by simp) : G.scheme ⟶ Over.mk (𝟙 S.left)) ≫ t)⁻¹ * 𝟙 G.scheme

def familyTranslation (t : Over.mk (𝟙 S.left) ⟶ G.scheme) : AbelianFamilyPoints.FamilyPoints.total S G ⟶ AbelianFamilyPoints.FamilyPoints.total S G :=
  FamilyEndomorphismCharts.Abelian.FamilyPoints.familyEndomorphism S G (translationEndomorphism S G t)

theorem familyTranslation_fiber (t : Over.mk (𝟙 S.left) ⟶ G.scheme)
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (u : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (familyTranslation S G t)
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) u) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s)
        ((fiberSection S G t s)⁻¹ * u) := by
  let e := G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
  have hs : e u ≫ (Over.homMk G.scheme.hom (by simp) : G.scheme ⟶ Over.mk (𝟙 S.left)) =
      sectionBasePoint S s := by
    apply Over.OverMorphism.ext
    exact (e u).w.trans (Category.id_comp _)
  have he : e u ≫ translationEndomorphism S G t = e ((fiberSection S G t s)⁻¹ * u) := by
    change e u ≫ (_⁻¹ * 𝟙 G.scheme) = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hs, Category.comp_id,
      map_mul, map_inv]
    exact congrArg (fun v => v⁻¹ * e u) (e.apply_symm_apply (sectionBasePoint S s ≫ t)).symm
  apply Over.OverMorphism.ext
  exact congrArg
    (fun w : G.Points ((Over.map s.left).obj (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) => w.left) he

theorem fiberSection_torsion (t : Over.mk (𝟙 S.left) ⟶ G.scheme)
    (n : ℕ) (ht : t ^ n = 1) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    fiberSection S G t s ^ n = 1 := by
  apply (G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))).injective
  rw [map_pow, map_one]
  change ((G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
    ((G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))).symm
      (sectionBasePoint S s ≫ t))) ^ n = 1
  rw [MulEquiv.apply_symm_apply, ← MonObj.comp_pow, ht, MonObj.comp_one]

theorem familyTranslation_continuous (t : Over.mk (𝟙 S.left) ⟶ G.scheme) :
    Continuous (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (familyTranslation S G t)) :=
  AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _

/-- Local uniqueness at the identity compares any continuous torsion
section to an actual algebraic torsion section of the same order. -/
theorem torsion_section_locally_eq_algebraic_of_unique
    {P : Type} [TopologicalSpace P] (parameter : P → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (p₀ : P)
    (n : ℕ)
    (hunique : ∀ z : ∀ p, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (parameter p).left).scheme,
      z p₀ = 1 →
      ContinuousAt (fun p => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
        (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (parameter p)) (z p)) p₀ →
      (∀ᶠ p in 𝓝 p₀, z p ^ n = 1) → ∀ᶠ p in 𝓝 p₀, z p = 1)
    (t : Over.mk (𝟙 S.left) ⟶ G.scheme) (ht : t ^ n = 1)
    (z : ∀ p, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback (parameter p).left).scheme)
    (hz₀ : z p₀ = fiberSection S G t (parameter p₀))
    (hzcont : ContinuousAt (fun p => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (parameter p)) (z p)) p₀)
    (hztorsion : ∀ᶠ p in 𝓝 p₀, z p ^ n = 1) :
    ∀ᶠ p in 𝓝 p₀, z p = fiberSection S G t (parameter p) := by
  let w := fun p => (fiberSection S G t (parameter p))⁻¹ * z p
  have hw₀ : w p₀ = 1 := by simp [w, hz₀]
  have hwcont : ContinuousAt (fun p => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) (parameter p)) (w p)) p₀ := by
    have h := (familyTranslation_continuous S G t).continuousAt.comp hzcont
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun p => (familyTranslation_fiber S G t (parameter p) (z p)).symm)
  have hwtorsion : ∀ᶠ p in 𝓝 p₀, w p ^ n = 1 := by
    filter_upwards [hztorsion] with p hp
    dsimp only [w]
    rw [mul_pow, inv_pow, fiberSection_torsion S G t n ht, hp, inv_one, one_mul]
  exact (hunique w hw₀ hwcont hwtorsion).mono (fun _ hp => (inv_mul_eq_one.mp hp).symm)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FamilyTranslations.Abelian.FamilyPoints
