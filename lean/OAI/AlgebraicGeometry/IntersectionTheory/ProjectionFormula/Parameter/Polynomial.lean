import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Polynomial -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial

noncomputable section

section

/-! The ordinary polynomial parameter line is the native affine
line, with its exact coefficient morphism and geometrically integral
fibers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

namespace Line

def base : Spec (.of ℂ[X]) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase := Spec.map (CommRingCat.ofHom Polynomial.C)

def iso : Spec (.of ℂ[X]) ≅ 𝔸(Unit; Foundations.Scheme.ProjectiveSpace.complexBase) :=
  Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv ℂ Unit).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso Unit (.of ℂ)).symm

theorem over_base : iso.hom ≫ (𝔸(Unit; Foundations.Scheme.ProjectiveSpace.complexBase) ↘ Foundations.Scheme.ProjectiveSpace.complexBase) = base := by
  change (Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv ℂ Unit).toRingHom) ≫
    (AffineSpace.SpecIso Unit (.of ℂ)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (MvPolynomial.uniqueAlgEquiv ℂ Unit).commutes c

theorem isPullback : IsPullback iso.hom base (𝔸(Unit; Foundations.Scheme.ProjectiveSpace.complexBase) ↘ Foundations.Scheme.ProjectiveSpace.complexBase) (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) :=
  IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact over_base⟩

instance geometricallyIntegral : GeometricallyIntegral base :=
  MorphismProperty.of_isPullback isPullback inferInstance

instance relativeDimension : SmoothOfRelativeDimension 1 base := by
  change SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* ℂ[X])))
  rw [← Projective.FamilyIs.MatrixParameterOpen.affine_over]
  let : SmoothOfRelativeDimension 1 (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) :=
    Projective.Dimension.projective_relativeDimension 1
  exact smoothOfRelativeDimension_comp Projective.FamilyIs.MatrixParameterOpen.affine
    (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) (n := 0) (m := 1)

instance smooth : Smooth base := SmoothOfRelativeDimension.smooth 1 base

end Line

end

section

/-! Product with the determinant-open parameter line preserves
integrality. The product is an actual open subscheme of an integral
affine-line bundle and has its genuine zero section. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

namespace IntegralProduct

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)

def parameterBase : Spec (.of (ProjectionFormula.Polynomial.MatrixPath.Ring A)) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  Spec.map (CommRingCat.ofHom (Projective.FamilySupport.Family.coefficients A))

def toLine : Spec (.of (ProjectionFormula.Polynomial.MatrixPath.Ring A)) ⟶ Spec (.of ℂ[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ[X] (ProjectionFormula.Polynomial.MatrixPath.Ring A)))

instance toLine_open : IsOpenImmersion (toLine A) :=
  IsOpenImmersion.of_isLocalization (ProjectionFormula.Polynomial.MatrixPath.determinant A)

theorem over_base : toLine A ≫ Line.base = parameterBase A := by
  rw [toLine, Line.base, ← Spec.map_comp]
  rfl

theorem scalar_retraction (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht)) ≫
    parameterBase A = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := by
  have he : (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht).comp (Projective.FamilySupport.Family.coefficients A) =
      RingHom.id ℂ := by
    apply RingHom.ext
    intro c
    exact (ProjectionFormula.Polynomial.MatrixPath.evaluation_algebraMap A t ht (Polynomial.C c)).trans Polynomial.eval_C
  rw [parameterBase, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht).comp
    (Projective.FamilySupport.Family.coefficients A))) = _
  rw [he]
  simp

theorem zero_retraction : Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A))) ≫
    parameterBase A = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := scalar_retraction A 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A)

variable {Z : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev space : Scheme := pullback (parameterBase A) f

def inclusion : space A f ⟶ pullback Line.base f :=
  pullback.map _ _ _ _ (toLine A) (𝟙 Z) (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    (by rw [Category.comp_id]; exact (over_base A).symm) (by simp)

instance inclusion_open : IsOpenImmersion (inclusion A f) := by
  unfold inclusion
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (toLine_open A) (inferInstanceAs (IsOpenImmersion (𝟙 Z)))
    (over_base A).symm (by simp)

def sectionZero : Z ⟶ space A f :=
  pullback.lift (f ≫ Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A)))) (𝟙 Z)
    (by rw [Category.assoc, zero_retraction, Category.comp_id, Category.id_comp])

instance nonempty [Nonempty Z] : Nonempty (space A f) :=
  ⟨sectionZero A f (Nonempty.some inferInstance)⟩

instance integral [IsIntegral Z] [IsLocallyNoetherian Z] : IsIntegral (space A f) := by
  let : IsIntegral (pullback Line.base f) := inferInstance
  exact isIntegral_of_isOpenImmersion (inclusion A f)

end IntegralProduct

end

/-! The determinant-open matrix family on an arbitrary projective
subscheme, with its actual base-change square and marked fibers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace ProjectiveSubschemeFamily

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
  {Z : Scheme} (i : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)

abbrev space : Scheme := pullback (Projective.FamilySupport.Family.projection A) i

def toAmbient : space A i ⟶ Projective.MatrixFamily.Family.space A := pullback.fst _ _

def toSource : space A i ⟶ Z := pullback.snd _ _

def parameter : space A i ⟶ Spec (.of (ProjectionFormula.Polynomial.MatrixPath.Ring A)) :=
  toAmbient A i ≫ Relative.ProjectiveI.Base.base (ProjectionFormula.Polynomial.MatrixPath.Ring A) n

theorem base_change : IsPullback (parameter A i) (toSource A i)
    (IntegralProduct.parameterBase A) (i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := by
  exact (IsPullback.of_hasPullback (Projective.FamilySupport.Family.projection A) i).paste_horiz
    (Relative.ProjectivePullback.isPullback
      (Projective.FamilySupport.Family.coefficients A) n).flip

def productIso : space A i ≅
    IntegralProduct.space A (i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) :=
  (base_change A i).isoPullback

def specialization (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) : Z ⟶ space A i :=
  pullback.lift (i ≫ Projective.MatrixFamily.Family.specialization A t ht) (𝟙 Z) (by
    rw [Category.assoc, Projective.FamilySupport.Family.specialization_projection,
      Category.comp_id, Category.id_comp])

theorem specialization_ambient (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    specialization A i t ht ≫ toAmbient A i =
      i ≫ Projective.MatrixFamily.Family.specialization A t ht := pullback.lift_fst _ _ _

theorem specialization_source (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    specialization A i t ht ≫ toSource A i = 𝟙 Z := pullback.lift_snd _ _ _

theorem specialization_parameter (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    specialization A i t ht ≫ parameter A i =
      (i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) ≫ Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht)) := by
  rw [parameter, ← Category.assoc, specialization_ambient, Category.assoc,
    Projective.MatrixFamily.Family.specialization_base, Category.assoc]

theorem fiber (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    IsPullback (specialization A i t ht) (i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
      (parameter A i) (Spec.map (CommRingCat.ofHom (ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht))) := by
  apply (IsPullback.paste_horiz_iff (base_change A i).flip
    (specialization_parameter A i t ht)).mp
  rw [specialization_source]
  rw [IntegralProduct.scalar_retraction]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

instance nonempty [Nonempty Z] : Nonempty (space A i) :=
  ⟨specialization A i 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A) (Nonempty.some inferInstance)⟩

instance integral [IsIntegral Z] [IsLocallyNoetherian Z] : IsIntegral (space A i) :=
  isIntegral_of_isOpenImmersion (productIso A i).hom

instance flat_parameter : Flat (parameter A i) :=
  MorphismProperty.of_isPullback (base_change A i).flip inferInstance

instance ambient_closed [IsClosedImmersion i] : IsClosedImmersion (toAmbient A i) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst _ i))

def moving : space A i ⟶ Projective.MatrixFamily.Family.space A :=
  toAmbient A i ≫ (Projective.MatrixFamily.Family.automorphism A).hom

instance moving_closed [IsClosedImmersion i] : IsClosedImmersion (moving A i) := by
  unfold moving
  infer_instance

theorem moving_parameter : moving A i ≫ Relative.ProjectiveI.Base.base (ProjectionFormula.Polynomial.MatrixPath.Ring A) n =
    parameter A i := by
  rw [moving, Category.assoc, Projective.MatrixFamily.Family.over_base]
  rfl

theorem moving_zero : specialization A i 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A) ≫ moving A i =
    i ≫ Projective.MatrixFamily.Family.specialization A 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A) := by
  rw [moving, ← Category.assoc, specialization_ambient, Category.assoc,
    Projective.MatrixFamily.Family.at_zero]

theorem moving_one : specialization A i 1 (ProjectionFormula.Polynomial.MatrixPath.one_good A) ≫ moving A i =
    (i ≫ Projective.LinearChart.Automorphism.map A) ≫
      Projective.MatrixFamily.Family.specialization A 1 (ProjectionFormula.Polynomial.MatrixPath.one_good A) := by
  rw [moving, ← Category.assoc, specialization_ambient, Category.assoc,
    Projective.MatrixFamily.Family.at_one, Category.assoc]

end ProjectiveSubschemeFamily

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial
