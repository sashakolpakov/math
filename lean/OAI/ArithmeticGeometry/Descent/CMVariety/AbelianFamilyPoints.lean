import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Abelian Family Points -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints

noncomputable section

/-!
Native topology of actual scheme fibers. The actual base change at a
complex point is homeomorphic to the topological fiber of the actual
map on complex points. The result is then specialized to abelian schemes.
No local topological trivialization is assumed or asserted.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

def fiber (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (pullback.snd p.left s.left)

def fiberInclusion (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : fiber p s ⟶ X :=
  Over.homMk (pullback.fst p.left s.left) (by
    change pullback.fst p.left s.left ≫ X.hom = pullback.snd p.left s.left
    rw [← Over.w p, ← Category.assoc, pullback.condition, Category.assoc, Over.w s]
    exact Category.comp_id _)

instance fiberInclusion_closed (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    IsClosedImmersion (fiberInclusion p s).left := by
  have : IsClosedImmersion s.left :=
    isClosedImmersion_of_comp_eq_id S.hom s.left s.w
  change IsClosedImmersion (pullback.fst p.left s.left)
  infer_instance

theorem fiberInclusion_range (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fiberInclusion p s)) =
      {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X | AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x = s} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    apply Over.OverMorphism.ext
    change (q.left ≫ pullback.fst p.left s.left) ≫ p.left = s.left
    erw [Category.assoc, pullback.condition, ← Category.assoc]
    have hq : q.left ≫ pullback.snd p.left s.left = 𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := q.w
    rw [hq]
    exact Category.id_comp s.left
  · intro hx
    have hx' : x.left ≫ p.left = s.left := congrArg Over.Hom.left hx
    have h : x.left ≫ p.left = (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ≫ s.left := by
      simpa only [Category.id_comp] using hx'
    let q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (fiber p s) :=
      Over.homMk (pullback.lift x.left (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) h) (by
        change pullback.lift x.left (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) h ≫ pullback.snd p.left s.left =
          𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase
        exact pullback.lift_snd _ _ _)
    refine ⟨q, ?_⟩
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- Actual scheme base change gives precisely the native topological fiber. -/
def fiberHomeomorph (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (fiber p s) ≃ₜ
      {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X // AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p x = s} :=
  (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    (fiberInclusion p s)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (fiberInclusion_range p s))

theorem fiberHomeomorph_apply (p : X ⟶ S) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (fiber p s)) :
    (fiberHomeomorph p s x).val = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fiberInclusion p s) x := rfl

/-- The total space of an abelian scheme over a complex base scheme. -/
def total {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (A.scheme.hom ≫ S.hom)

def projection {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) :
    total S A ⟶ S := Over.homMk A.scheme.hom rfl

/-- The genuine algebraic identity section of the abelian scheme,
regarded over the complex base. -/
def identitySection {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) :
    S ⟶ total S A :=
  Over.homMk (1 : Over.mk (𝟙 S.left) ⟶ A.scheme).left (by
    change (1 : Over.mk (𝟙 S.left) ⟶ A.scheme).left ≫ (A.scheme.hom ≫ S.hom) = S.hom
    rw [← Category.assoc, Over.w]
    exact Category.id_comp S.hom)

theorem identitySection_projection {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) : identitySection S A ≫ projection S A = 𝟙 S := by
  apply Over.OverMorphism.ext
  exact (1 : Over.mk (𝟙 S.left) ⟶ A.scheme).w

/-- The actual native point map of the identity section is continuous
and is a section of the actual native family projection. -/
theorem native_identitySection {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) :
    Continuous (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (identitySection S A)) ∧
      Function.RightInverse (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (identitySection S A))
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (projection S A)) := by
  refine ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _, fun s => ?_⟩
  change (s ≫ identitySection S A) ≫ projection S A = s
  rw [Category.assoc, identitySection_projection, Category.comp_id]

/-- This is the literal base-change fiber of the actual abelian scheme,
with its existing native topology on complex points. -/
def abelianFiberHomeomorph {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A.pullback s.left).scheme ≃ₜ
      {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (total S A) // AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (projection S A) x = s} :=
  fiberHomeomorph (projection S A) s

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints
