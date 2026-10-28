import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseTranslations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Morphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentingIsoPoints

/-! # Translation Labels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The geometric full-level labels agree with the torsion points used to construct the translation action on functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)

theorem Abelian.Schemes.AbelianScheme.fullLevelSchemeIso_point {T : Over S} (p : T ⟶ Level.Scheme.constantFullLevelScheme g N S) :
    A.torsionSchemePointsEquiv N T (p ≫ level.schemeIso.hom) =
      (level.hom.app (.op T)) ((Level.Scheme.constantFullLevelRepresentable g N S).homEquiv p) :=
  RepresentingIsoPoints.representingIso_homEquiv
    ((Level.Scheme.constantFullLevelRepresentable g N S).ofIso
      (Functor.isoWhiskerRight level (forget GrpCat))) (A.torsionRepresentable N) p

theorem Abelian.Schemes.AbelianScheme.fullLevelSchemeIso_label
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    ConstantScheme.Morphisms.constantSchemeLabelPoint S _ i ≫ level.schemeIso.hom ≫ A.torsionInclusion N =
      (A.fullLevelBaseTorsionPoints level i).val := by
  have hc : (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv (ConstantScheme.Morphisms.constantSchemeLabelPoint S _ i) =
      LocallyConstant.const S i.down := by
    apply LocallyConstant.ext
    intro x
    exact congrArg ULift.down (ConstantScheme.Iff.constantSchemeIndex_ι i x)
  have h := congrArg (fun a : A.torsionPoints N (𝟙_ (Over S)) => a.val)
    (A.fullLevelSchemeIso_point level (ConstantScheme.Morphisms.constantSchemeLabelPoint S _ i))
  rw [hc] at h
  exact (Category.assoc _ _ _).symm.trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
