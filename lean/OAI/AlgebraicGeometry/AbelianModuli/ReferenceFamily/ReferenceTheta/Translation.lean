import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationFactor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel
import OAI.RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation
import OAI.RepresentationTheory.Theta.Geometric.TranslationAlgebraization

/-! # Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Every lift in the actual polarization dual lattice acts on theta
sections by an explicit gauge and preserves their algebraic hyperplane
bundles on the chosen reference abelian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

section

theorem Reference.Fiber.ReferenceAnalyticFiber.dualTranslation_automorphy (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (a : F.dualLattice) (l : F.periodData.periodIntegerLattice) (w : Reference.Fiber.ReferenceTangent s) :
    RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge F.form a.val
        (@HAdd.hAdd (Reference.Fiber.ReferenceTangent s) (Reference.Fiber.ReferenceTangent s) (Reference.Fiber.ReferenceTangent s) inferInstance w l.val) *
        (F.polarizationFactor hP).value l
          (@HAdd.hAdd (Reference.Fiber.ReferenceTangent s) (Reference.Fiber.ReferenceTangent s) (Reference.Fiber.ReferenceTangent s) inferInstance w a.val) =
      (F.polarizationFactor hP).value l w * RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge F.form a.val w := by
  have hint : ∃ m : ℤ, (F.form a.val (F.latticeEmbedding (F.integralLatticeEquiv.symm l))).im = (m : ℝ) := by
    rw [F.latticeEmbedding_symm]
    obtain ⟨m, hm⟩ := Submodule.mem_one.mp (a.property l.val l.property)
    exact ⟨m, hm.symm⟩
  have h := RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge_automorphy (P.referenceBasis hP) P.integralForm
    F.latticeEmbedding F.form F.hermitian a.val (F.integralLatticeEquiv.symm l) hint w
  rw [F.latticeEmbedding_symm] at h
  exact h

def Reference.Fiber.ReferenceAnalyticFiber.dualTranslateSection (F : Reference.Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (a : F.dualLattice) {n : ℕ} (t : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (F.polarizationFactor hP) n) :
    RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (F.polarizationFactor hP) n :=
  t.translateByGauge a.val (RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge F.form a.val)
    ((RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge_contDiff F.form a.val).of_le (by norm_num))
    (F.dualTranslation_automorphy hP a)

end

variable (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslation_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslation_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.kernel_hyperplane_iso (U : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (hUi : Function.Injective U.projectiveMap)
    (hUd : ∀ p v : F.periodData.space, v ≠ 0 → U.Detects p v)
    (j : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (he : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) (a : F.dualLattice) :
    Nonempty (((HilbertConstruction.Line.Bundles.LineBundle.pullback j.left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicTwistBundle U.projectiveDimension 1)).pullback
      (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.period (QuotientAddGroup.mk a.val))).left).sheaf ≅
      (HilbertConstruction.Line.Bundles.LineBundle.pullback j.left (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicTwistBundle U.projectiveDimension 1)).sheaf) :=
  RepresentationTheory.Theta.Geometric.TranslationAlgebraization.thetaTranslation_algebraic_iso U hUi hUd (F.dualTranslateSection hP a) a.val
    (RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge F.form a.val) (RepresentationTheory.Theta.Geometric.Dual.LatticeTranslation.polarizationTranslationGauge_ne_zero F.form a.val)
    (fun _ _ => rfl) M.abelian M.period M.period_add j he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
