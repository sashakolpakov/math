import OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology

/-! # Support Points -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportPoints.Constructions

noncomputable section

/-! The actual analytic point space of a reduced product support is the
Cartesian product of the actual analytic point spaces of its two factors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def supportPointSet (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : IrreducibleCloseds X.left) :
    Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (A : Set X.left)

def supportOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : IrreducibleCloseds X.left) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Geometric.SupportFiniteType.supportStructureMap A X.hom)

def supportOverInclusion (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : IrreducibleCloseds X.left) :
    supportOver X A ⟶ X := Over.homMk (Geometric.GenericPoint.reducedSupportι A) rfl

instance supportOverInclusion_closed (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : IrreducibleCloseds X.left) :
    IsClosedImmersion (supportOverInclusion X A).left :=
  inferInstanceAs (IsClosedImmersion (Geometric.GenericPoint.reducedSupportι A))

def supportPointsHomeomorph (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : IrreducibleCloseds X.left) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (supportOver X A) ≃ₜ supportPointSet X A :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.immersionPointHomeomorph (supportOverInclusion X A)).trans
    (Homeomorph.setCongr (congrArg (fun S : Set X.left => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S)
      (Geometric.GenericPoint.range_reducedSupportι A)))

@[simp]
theorem supportPointsHomeomorph_val (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : IrreducibleCloseds X.left)
    (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (supportOver X A)) :
    (supportPointsHomeomorph X A z).val = z ≫ supportOverInclusion X A := rfl

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : IrreducibleCloseds X.left) (B : IrreducibleCloseds Y.left)
  (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY)) [LocallyOfFiniteType X.hom]

theorem productSupportPointSet :
    supportPointSet Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) =
      (PresentationPoints.Constructions.productPresentationPointsHomeomorph X Y Z πX πY hprod) ⁻¹'
        (supportPointSet X A ×ˢ supportPointSet Y B) := by
  ext z
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈
    (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod : Set Z.left) ↔ _
  rw [SupportScheme.Constructions.productIrreducibleSupport_coe]
  rfl

def productSupportSubsetHomeomorph :
    supportPointSet Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ≃ₜ
      (supportPointSet X A × supportPointSet Y B) :=
  ((PresentationPoints.Constructions.productPresentationPointsHomeomorph X Y Z πX πY hprod).subtype (fun z =>
    Set.ext_iff.mp (productSupportPointSet X Y A B Z πX πY hprod) z)).trans
    (Homeomorph.Set.prod (supportPointSet X A) (supportPointSet Y B))

def productSupportPointsHomeomorph :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (supportOver Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod)) ≃ₜ
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (supportOver X A) × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (supportOver Y B)) :=
  (supportPointsHomeomorph Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod)).trans
    ((productSupportSubsetHomeomorph X Y A B Z πX πY hprod).trans
      ((supportPointsHomeomorph X A).symm.prodCongr (supportPointsHomeomorph Y B).symm))

theorem productSupportPointsHomeomorph_fst
    (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (supportOver Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod))) :
    (productSupportPointsHomeomorph X Y A B Z πX πY hprod z).1 ≫ supportOverInclusion X A =
      z ≫ supportOverInclusion Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ≫ πX := by
  change (supportPointsHomeomorph X A
    ((supportPointsHomeomorph X A).symm _)).val = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem productSupportPointsHomeomorph_snd
    (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (supportOver Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod))) :
    (productSupportPointsHomeomorph X Y A B Z πX πY hprod z).2 ≫ supportOverInclusion Y B =
      z ≫ supportOverInclusion Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ≫ πY := by
  change (supportPointsHomeomorph Y B
    ((supportPointsHomeomorph Y B).symm _)).val = _
  rw [Homeomorph.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportPoints.Constructions
