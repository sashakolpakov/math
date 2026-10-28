import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.AlgebraicTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedLabelCongruence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers

/-! # Level Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.LevelTransport.ReferenceAlgebraicModel

noncomputable section

/-! The algebraized reference transport acts on the actual exponential
division points. Equality of the fixed lattice labels therefore gives
preservation of the original full level on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z w : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {G : Reference.Fiber.ReferenceAnalyticFiber P w}
    {hP : P.IsAdmissible} (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (W : Reference.AlgebraicModel.ReferenceAlgebraicModel G hP)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (hw : w.val = P.lineAction g z.val) (hΛ : ∀ v, v ∈ P.lattice ↔ g v ∈ P.lattice)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : IsIntegral W.abelian.toOver.left := W.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance : Smooth W.abelian.toOver.hom := W.abelian.variety.presentation.smooth

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceIso_levelPoint (N : ℕ) [NeZero N] (v : P.lattice) :
    (((M.fixedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP N v)))).val ≫
        (M.nativeReferenceIso W g hg hw hΛ).hom =
    (((W.fixedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase
        (Multiplicative.ofAdd (P.fixedLevelLabel hP N ⟨g v.val, (hΛ v.val).mp v.property⟩)))).val := by
  rw [M.fixedFullLevel_native_reference, W.fixedFullLevel_native_reference]
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (M.nativeReferenceIso W g hg hw hΛ).hom
    (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      ((N : ℝ)⁻¹ • (M.nativeReferenceMarking v.val).val)) = _
  rw [Intrinsic.LiftDifferential.IntrinsicLinearMaps.linearLift_exp]
  have hs := ((Intrinsic.Maps.IntrinsicLinearMaps.linearLift (M.nativeReferenceIso W g hg hw hΛ).hom).restrictScalars ℝ).map_smul
    (N : ℝ)⁻¹ (M.nativeReferenceMarking v.val).val
  have hv := congrArg Subtype.val (M.nativeReferenceIso_marking W g hg hw hΛ v.val)
  exact congrArg (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints W.abelian.toOver))
    (hs.trans (congrArg (fun x : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel W.abelian => (N : ℝ)⁻¹ • x) hv))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceIso_level (N : ℕ) [NeZero N]
    (hl : ∀ v : P.lattice, P.fixedLevelLabel hP N ⟨g v.val, (hΛ v.val).mp v.property⟩ =
      P.fixedLevelLabel hP N v)
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients (3 * s) N)) :
    ((M.fixedFullLevel N).hom.app (.op T) c).val ≫ (M.nativeReferenceIso W g hg hw hΛ).hom =
      ((W.fixedFullLevel N).hom.app (.op T) c).val := by
  let f : M.abelianScheme.scheme ⟶ W.abelianScheme.scheme := (M.nativeReferenceIso W g hg hw hΛ).hom
  let : IsMonHom f := M.nativeReferenceIso_isMonHom W g hg hw hΛ
  apply Level.Stabilizers.LevelCover.level_comparison_of_base_constants (M.fixedFullLevel N) (W.fixedFullLevel N)
    f ?_ T c
  intro a
  obtain ⟨v, hv⟩ := P.fixedLevelLabel_surjective hP N a.toAdd
  have he := M.nativeReferenceIso_levelPoint W g hg hw hΛ N v
  rw [hl, hv] at he
  exact he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.LevelTransport.ReferenceAlgebraicModel
