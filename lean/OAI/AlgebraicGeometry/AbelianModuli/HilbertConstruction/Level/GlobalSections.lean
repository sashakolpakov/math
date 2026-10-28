import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GeometricConfiguration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every ordered full-level label gives an actual global section of
the abelian family. The sections commute with arbitrary base change and
recover the previously constructed rational torsion points over fields. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S T : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.fullLevelGlobalSection (level : A.FullLevel n)
    (c : Multiplicative (Fin (2 * g) → ZMod n)) : S ⟶ A.scheme.left :=
  (level.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c)).val.left

theorem Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_comp (level : A.FullLevel n)
    (c : Multiplicative (Fin (2 * g) → ZMod n)) :
    A.fullLevelGlobalSection level c ≫ A.scheme.hom = 𝟙 S :=
  (level.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c)).val.w

theorem Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_pullback (level : A.FullLevel n) (q : T ⟶ S)
    (c : Multiplicative (Fin (2 * g) → ZMod n)) :
    (A.pullback q).fullLevelGlobalSection (level.pullback q) c ≫ pullback.fst A.scheme.hom q =
      q ≫ A.fullLevelGlobalSection level c := by
  let Z : Over T := Over.mk (𝟙 T)
  let u : (Over.map q).obj Z ⟶ Over.mk (𝟙 S) := Over.homMk q (by simp [Z])
  have hn := ConcreteCategory.congr_hom (level.hom.naturality u.op) (LocallyConstant.const S c)
  have hn' := congrArg (fun z => z.val.left) hn
  change (level.hom.app (.op ((Over.map q).obj Z)) (LocallyConstant.const T c)).val.left =
    q ≫ A.fullLevelGlobalSection level c at hn'
  have hb := congrArg Over.Hom.left (level.pullback_basis q Z (LocallyConstant.const T c))
  exact hb.trans hn'

theorem Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_field
    {K : Type u} [Field K] (B : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : B.FullLevel n)
    (c : Multiplicative (Fin (2 * g) → ZMod n)) :
    B.fullLevelGlobalSection level c = ((B.fullLevelRationalTorsionEquiv level).symm c).val.left := rfl

theorem Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_geometricPoint
    {K : Type u} [Field K] (B : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : B.FullLevel n)
    (c : Multiplicative (Fin (2 * g) → ZMod n)) :
    B.fullLevelGlobalSection level c (IsLocalRing.closedPoint K) = B.fullLevelGeometricPoint level c := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
