import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint

/-! # Frobenius Point Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusPointAction.CM

noncomputable section

/-! The actual algebraic Albanese Frobenius acts on geometric points
by the same field Frobenius used in FrobeniusKernel. This identifies the point
operator independently of the ordinary-kernel quotient calculation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable (q : ℕ) [Fact q.Prime]

theorem geometricBase_frobenius :
    FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) = (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom := by
  apply Over.OverMorphism.ext
  change FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius (ZMod q) (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))
      (FormalGeometry.Completion.Frobenius.Construction.varietyBaseMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)) =
    Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquiv (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q).toRingHom)
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))).inv ≫
      (FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius (ZMod q) (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))
        (FormalGeometry.Completion.Frobenius.Construction.varietyBaseMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q))).appTop =
    (Scheme.ΓSpecIso (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))).inv ≫
      (Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquiv (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q).toRingHom)).appTop
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext r
  exact (map_pow (Scheme.ΓSpecIso (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))).inv.hom r
    (Fintype.card (ZMod q))).symm

variable (G : CommGrp (Over (Spec (.of (ZMod q)))))

theorem frobenius_evaluation (p : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ G.X) :
    PointSpecializationFormula.CM.Points.evaluateAt G (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) (Finite.FieldFrobenius.CM.integralFrobenius G) (Additive.ofMul p) =
      Additive.ofMul ((AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ p) := by
  apply Additive.toMul.injective
  exact (AbelianScheme.TateComparison.End.endSchemeMap_points G.X (Finite.FieldFrobenius.CM.integralFrobenius G) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) p).trans
    ((congrArg (p ≫ ·) (FrobeniusComparison.CM.integralFrobenius_schemeMap G)).trans
      ((FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius_naturality (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) p).symm.trans
        (congrArg (· ≫ p) (geometricBase_frobenius q))))

theorem frobenius_albanese_point {X : Over (Spec (.of (ZMod q)))}
    (a : X ⟶ G.X) (p : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ X) :
    PointSpecializationFormula.CM.Points.evaluateAt G (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) (Finite.FieldFrobenius.CM.integralFrobenius G) (Additive.ofMul (p ≫ a)) =
      Additive.ofMul (((AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ p) ≫ a) :=
  (frobenius_evaluation q G (p ≫ a)).trans
    (congrArg Additive.ofMul (Category.assoc _ _ _).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusPointAction.CM
