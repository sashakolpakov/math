import OAI.RepresentationTheory.Theta.Geometric.Reference.TateFrame
import OAI.RepresentationTheory.Theta.Geometric.Local.MatrixLattice

/-! # Reference Tate Map -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual rational Tate map of a cleared reference isogeny is the
prescribed scalar times the original matrix on every local block. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x y : D.domain}

def Data.ActiveHeckeThetaData.localMatrixAction (g : D.RationalSU) : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateSpace s q →ₗ[ℚ_[q]] AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateSpace s q :=
  LinearMap.pi (fun v => (D.localMatrix v g).val.mulVecLin.comp (LinearMap.proj v))

theorem Data.ActiveHeckeThetaData.localMatrixAction_apply (g : D.RationalSU) (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateSpace s q) (v : Fin s × Bool) :
    Data.ActiveHeckeThetaData.localMatrixAction g u v = (D.localMatrix v g).val.mulVec (u v) := rfl

theorem Data.ActiveHeckeThetaData.localMatrixAction_reference (g : D.RationalSU) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Data.ActiveHeckeThetaData.localMatrixAction g (D.jointLocalEmbedding u) = D.jointLocalEmbedding (D.rationalLinear g u) := by
  funext v
  exact D.localMatrix_reference_action g v u

attribute [local irreducible] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame

theorem Data.ActiveHeckeThetaData.cleared_referenceTateMap
    (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)
    (N : D.PeriodModel hg y) (G : D.ReferenceAnalyticFiber y)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hc : D.HasFiniteCoordinates)
    (f : M.abelian.toOver ⟶ N.abelian.toOver) [IsMonHom f] (n : ℕ) (g : D.RationalSU)
    (ht : ∀ u, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f ((M.toNativeReferenceModel F).nativeReferenceMarking u) =
      (N.toNativeReferenceModel G).nativeReferenceMarking ((q : ℤ) ^ n • D.rationalLinear g u)) :
    (N.referenceTateFrame G hgood hdegree).toLinearMap.comp
      (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f) =
      ((q : ℚ_[q]) ^ n • Data.ActiveHeckeThetaData.localMatrixAction g).comp
        (M.referenceTateFrame F hgood hdegree).toLinearMap := by
  apply M.referenceTate_linear_ext F
  intro z u
  change N.referenceTateFrame G hgood hdegree
    (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f
      (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q
        (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking u))) =
    (q : ℚ_[q]) ^ n • Data.ActiveHeckeThetaData.localMatrixAction g
      (M.referenceTateFrame F hgood hdegree
        (AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv M.abelian q
          (z ⊗ₜ[ℚ] (M.toNativeReferenceModel F).nativeReferenceMarking u)))
  rw [M.referenceTateFrame_map_marking F N G hgood hdegree hc f
    (fun u => (q : ℤ) ^ n • D.rationalLinear g u) ht,
    M.referenceTateFrame_marking F hgood hdegree hc, map_smul, Data.ActiveHeckeThetaData.localMatrixAction_reference]
  funext v i
  change z * D.localEmbedding v ((q : ℤ) ^ n • D.rationalLinear g u i) =
    (q : ℚ_[q]) ^ n * (z * D.localEmbedding v (D.rationalLinear g u i))
  rw [map_zsmul, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
  ring

theorem Data.ActiveHeckeThetaData.cleared_referenceTateMap_apply
    (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)
    (N : D.PeriodModel hg y) (G : D.ReferenceAnalyticFiber y)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hc : D.HasFiniteCoordinates)
    (f : M.abelian.toOver ⟶ N.abelian.toOver) [IsMonHom f] (n : ℕ) (g : D.RationalSU)
    (ht : ∀ u, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f ((M.toNativeReferenceModel F).nativeReferenceMarking u) =
      (N.toNativeReferenceModel G).nativeReferenceMarking ((q : ℤ) ^ n • D.rationalLinear g u))
    (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule M.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q) (v : Fin s × Bool) :
    N.referenceTateFrame G hgood hdegree
      (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f u) v =
      (q : ℚ_[q]) ^ n • (D.localMatrix v g).val.mulVec
        (M.referenceTateFrame F hgood hdegree u v) :=
  congrFun (LinearMap.congr_fun (Data.ActiveHeckeThetaData.cleared_referenceTateMap M F N G hgood hdegree hc f n g ht) u) v

end

end OAI.RepresentationTheory.Theta.Geometric
