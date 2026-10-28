import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FiberComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers

/-! # Model Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelComparison

noncomputable section

/-! Reference algebraizations are isomorphic by actual scheme maps.
The constructed comparison preserves the integral action and the fixed
ordered level over every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F G : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom := A.variety.presentation.projective.isProper

namespace ReferenceAlgebraicModel

variable (M : AlgebraicModel.ReferenceAlgebraicModel F hP) (D : AlgebraicModel.ReferenceAlgebraicModel G hP)

local instance : IsIntegral M.abelianScheme.scheme.left := M.abelian.variety.property
local instance : IsProper M.abelianScheme.scheme.hom := M.abelian.variety.presentation.projective.isProper
local instance : IsIntegral D.abelianScheme.scheme.left := D.abelian.variety.property
local instance : IsProper D.abelianScheme.scheme.hom := D.abelian.variety.presentation.projective.isProper

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.exists_comparison : ∃ e : M.abelianScheme.scheme ≅ D.abelianScheme.scheme,
    IsMonHom e.hom ∧ ∀ t,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (M.period t) = D.period (F.torusMap G t) := by
  obtain ⟨f, hf, hfp⟩ := RepresentationTheory.Theta.Geometric.Torus.Hom.exists_algebraic_torus_map F.periodData G.periodData
    (F.tangentEquiv G).toLinearMap (F.tangentEquiv_lattice G)
    M.abelian D.abelian M.period D.period M.period_add D.period_add
  obtain ⟨g, _, hgp⟩ := RepresentationTheory.Theta.Geometric.Torus.Hom.exists_algebraic_torus_map G.periodData F.periodData
    (G.tangentEquiv F).toLinearMap (G.tangentEquiv_lattice F)
    D.abelian M.abelian D.period M.period D.period_add M.period_add
  change ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) = D.period (F.torusMap G t) at hfp
  change ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (D.period t) = M.period (G.torusMap F t) at hgp
  have hfg : f ≫ g = 𝟙 M.abelian.toOver := by
    apply Albanese.Construction.ClosedPoints.hom_ext_of_points
    intro p
    obtain ⟨t, rfl⟩ := M.period.surjective p
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t)) = M.period t
    rw [hfp, hgp, F.torusMap_reverse G]
  have hgf : g ≫ f = 𝟙 D.abelian.toOver := by
    apply Albanese.Construction.ClosedPoints.hom_ext_of_points
    intro p
    obtain ⟨t, rfl⟩ := D.period.surjective p
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (D.period t)) = D.period t
    rw [hgp, hfp, G.torusMap_reverse F]
  exact ⟨⟨f, g, hfg, hgf⟩, hf, hfp⟩

variable {M D}

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.comparison_action (e : M.abelianScheme.scheme ≅ D.abelianScheme.scheme)
    (he : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (M.period t) = D.period (F.torusMap G t))
    (a : NumberField.RingOfIntegers E) :
    M.integralAction.map a ≫ e.hom = e.hom ≫ D.integralAction.map a := by
  apply Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  obtain ⟨t, rfl⟩ := M.period.surjective p
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) (M.period t)) =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap D.abelian.toOver (D.functorAction a))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (M.period t))
  let f : M.abelian.toOver ⟶ D.abelian.toOver := e.hom
  exact (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (M.period_action a t)).trans
    ((he (F.quotientAction hP a t)).trans
      ((congrArg D.period (F.torusMap_action G hP a t)).trans
        ((D.period_action a (F.torusMap G t)).symm.trans
          (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
            (AbelianScheme.TateComparison.End.endSchemeMap D.abelian.toOver (D.functorAction a))) (he t).symm))))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.comparison_level (e : M.abelianScheme.scheme ≅ D.abelianScheme.scheme) [IsMonHom e.hom]
    (he : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (M.period t) = D.period (F.torusMap G t))
    (N : ℕ) [NeZero N] (T : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (c : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients (3 * s) N)) :
    ((M.fixedFullLevel N).hom.app (.op T) c).val ≫ e.hom =
      ((D.fixedFullLevel N).hom.app (.op T) c).val := by
  apply Level.Stabilizers.LevelCover.level_comparison_of_base_constants
  intro a
  obtain ⟨v, hv⟩ := P.fixedLevelLabel_surjective hP N a.toAdd
  have ha : Multiplicative.ofAdd (P.fixedLevelLabel hP N v) = a := congrArg Multiplicative.ofAdd hv
  rw [← ha, M.fixedFullLevel_reference, D.fixedFullLevel_reference]
  exact (he (F.divisionPoint N v)).trans (congrArg D.period (F.torusMap_division G N v))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.comparison_unique (e f : M.abelianScheme.scheme ⟶ D.abelianScheme.scheme)
    (he : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e (M.period t) = D.period (F.torusMap G t))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) = D.period (F.torusMap G t)) : e = f := by
  apply Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  obtain ⟨t, rfl⟩ := M.period.surjective p
  exact (he t).trans (hf t).symm

end ReferenceAlgebraicModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelComparison
