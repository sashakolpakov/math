import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationGeometricCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.MorphismRestrictedPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # Pullback Preservation Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PullbackPreservationCriterion

noncomputable section

/-! Equality of the pulled-back finite level maps is exactly preservation of the pulled-back full level on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem fullLevel_pullback_preserves_iff
    {S T : Scheme.{u}} {g N : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (l : A.FullLevel N) (k : B.FullLevel N) (f : A.scheme ⟶ B.scheme) (b : T ⟶ S) :
    (Over.pullback b).map (l.schemeIso.hom ≫ A.torsionInclusion N ≫ f) =
      (Over.pullback b).map (k.schemeIso.hom ≫ B.torsionInclusion N) ↔
    ∀ (U : Over T) (c : LocallyConstant U.left (Multiplicative (Fin (2 * g) → ZMod N))),
      ((l.pullback b).hom.app (.op U) c).val ≫ (Over.pullback b).map f =
        ((k.pullback b).hom.app (.op U) c).val := by
  rw [Pullback.MorphismRestrictedPoints.pullback_map_eq_iff_restrictedPoints]
  constructor
  · intro h U c
    let z : (Over.map b).obj U ⟶ Level.Scheme.constantFullLevelScheme g N S :=
      (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv.symm c
    have H := h U z
    have hl := PreservationGeometricCriterion.fullLevel_point_from_geometric l ((Over.map b).obj U) c
    have hk := PreservationGeometricCriterion.fullLevel_point_from_geometric k ((Over.map b).obj U) c
    have H' : (z ≫ l.schemeIso.hom ≫ A.torsionInclusion N) ≫ f =
        z ≫ k.schemeIso.hom ≫ B.torsionInclusion N := by
      simpa only [Category.assoc] using H
    have H'' := (congrArg (fun w => w ≫ f) hl).symm.trans (H'.trans hk)
    apply (B.baseChangePointsEquiv b U).injective
    exact (Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f b U ((l.pullback b).hom.app (.op U) c).val).trans
      ((congrArg (fun z => z ≫ f) (l.pullback_basis b U c)).trans
        (H''.trans (k.pullback_basis b U c).symm))
  · intro h U z
    let c : LocallyConstant U.left (Multiplicative (Fin (2 * g) → ZMod N)) :=
      (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv z
    have H : (l.hom.app (.op ((Over.map b).obj U)) c).val ≫ f =
        (k.hom.app (.op ((Over.map b).obj U)) c).val :=
      (congrArg (fun z => z ≫ f) (l.pullback_basis b U c)).symm.trans
        ((Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f b U ((l.pullback b).hom.app (.op U) c).val).symm.trans
          ((congrArg (B.baseChangePointsEquiv b U) (h U c)).trans (k.pullback_basis b U c)))
    have hl : z ≫ l.schemeIso.hom ≫ A.torsionInclusion N = (l.hom.app (.op ((Over.map b).obj U)) c).val := by
      simpa only [c, Equiv.symm_apply_apply] using PreservationGeometricCriterion.fullLevel_point_from_geometric l ((Over.map b).obj U) c
    have hk : z ≫ k.schemeIso.hom ≫ B.torsionInclusion N = (k.hom.app (.op ((Over.map b).obj U)) c).val := by
      simpa only [c, Equiv.symm_apply_apply] using PreservationGeometricCriterion.fullLevel_point_from_geometric k ((Over.map b).obj U) c
    calc
      z ≫ l.schemeIso.hom ≫ A.torsionInclusion N ≫ f =
          (z ≫ l.schemeIso.hom ≫ A.torsionInclusion N) ≫ f := by simp only [Category.assoc]
      _ = (l.hom.app (.op ((Over.map b).obj U)) c).val ≫ f := congrArg (fun w => w ≫ f) hl
      _ = (k.hom.app (.op ((Over.map b).obj U)) c).val := H
      _ = z ≫ k.schemeIso.hom ≫ B.torsionInclusion N := hk.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PullbackPreservationCriterion
