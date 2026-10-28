import OAI.ArithmeticGeometry.Descent.CMVariety.LevelComparison
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods

/-! # Presented Level -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! Full-level transport through actual geometric fiber presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable {g : ℕ} {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

def StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso (P : StandardModuli.Abelian.ComplexAbelianPresentation A) (Q : StandardModuli.Abelian.ComplexAbelianPresentation B)
    (e : P.variety.toOver ≅ Q.variety.toOver) : A.scheme ≅ B.scheme :=
  P.comparison ≪≫ e ≪≫ Q.comparison.symm

instance StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso_group (P : StandardModuli.Abelian.ComplexAbelianPresentation A) (Q : StandardModuli.Abelian.ComplexAbelianPresentation B)
    (e : P.variety.toOver ≅ Q.variety.toOver) [IsMonHom e.hom] :
    IsMonHom (StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso P Q e).hom := by
  let : IsMonHom P.comparison.hom := P.comparison_group
  let : IsMonHom Q.comparison.hom := Q.comparison_group
  change IsMonHom (P.comparison.hom ≫ e.hom ≫ Q.comparison.inv)
  infer_instance

def StandardModuli.Abelian.ComplexAbelianPresentation.FullLevelCompatible (P : StandardModuli.Abelian.ComplexAbelianPresentation A) (Q : StandardModuli.Abelian.ComplexAbelianPresentation B)
    {n : ℕ} (levelA : A.FullLevel n) (levelB : B.FullLevel n)
    (e : P.variety.toOver ≅ Q.variety.toOver) : Prop :=
  ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (a : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod n))),
    (levelA.hom.app (.op T) a).val ≫ (StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso P Q e).hom = (levelB.hom.app (.op T) a).val

def StandardModuli.Abelian.ComplexAbelianPresentation.MarkedLevelReferences {Index : Type} [Fintype Index]
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A) {n : ℕ} (level : A.FullLevel n)
    (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index P.variety)
    (z : Multiplicative (Fin (2 * g) → ZMod n) → Index → ℂ) : Prop :=
  ∀ a, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom
    ((level.hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization P.variety ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus P.variety).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (z a)))

theorem StandardModuli.Abelian.ComplexAbelianPresentation.fullLevel_preserved_of_presented_labels
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A) (Q : StandardModuli.Abelian.ComplexAbelianPresentation B)
    {n : ℕ} (levelA : A.FullLevel n) (levelB : B.FullLevel n)
    (e : P.variety.toOver ≅ Q.variety.toOver) [IsMonHom e.hom]
    (h : ∀ a : Multiplicative (Fin (2 * g) → ZMod n),
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom
          ((levelA.hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))))
            (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map Q.comparison.hom
        ((levelB.hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))))
          (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val) :
    levelA.transport (StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso P Q e) = levelB := by
  apply LevelComparison.Abelian.fullLevel_transport_eq_of_constant_sections
  intro a
  have ha := h a
  change ((_ ≫ P.comparison.hom) ≫ e.hom) = _ ≫ Q.comparison.hom at ha
  have hb := congrArg (fun u : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Q.variety.toOver => u ≫ Q.comparison.inv) ha
  simpa only [StandardModuli.Abelian.ComplexAbelianPresentation.fiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Q.comparison.hom_inv_id, Category.comp_id] using hb

theorem StandardModuli.Abelian.ComplexAbelianPresentation.fullLevelCompatible_of_marked_references
    {Index : Type} [Fintype Index]
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A) (Q : StandardModuli.Abelian.ComplexAbelianPresentation B)
    {n : ℕ} (levelA : A.FullLevel n) (levelB : B.FullLevel n)
    (bA : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index P.variety) (bB : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index Q.variety)
    (z : Multiplicative (Fin (2 * g) → ZMod n) → Index → ℂ)
    (hA : StandardModuli.Abelian.ComplexAbelianPresentation.MarkedLevelReferences P levelA bA z) (hB : StandardModuli.Abelian.ComplexAbelianPresentation.MarkedLevelReferences Q levelB bB z)
    (e : P.variety.toOver ≅ Q.variety.toOver) [IsMonHom e.hom]
    (hp : ∀ v : Index → ℂ,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization P.variety ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus P.variety).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap bA v))) =
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization Q.variety ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus Q.variety).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap bB v))) :
    StandardModuli.Abelian.ComplexAbelianPresentation.FullLevelCompatible P Q levelA levelB e := by
  have h := StandardModuli.Abelian.ComplexAbelianPresentation.fullLevel_preserved_of_presented_labels P Q levelA levelB e (fun a => by
    rw [hA a, hB a]
    exact hp (z a))
  intro T a
  exact congrArg (fun level : B.FullLevel n => (level.hom.app (.op T) a).val) h

end

end OAI.ArithmeticGeometry.Descent.CMVariety
