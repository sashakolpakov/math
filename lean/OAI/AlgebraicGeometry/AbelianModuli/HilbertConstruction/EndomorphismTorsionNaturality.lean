import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismTorsionAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps

/-! # Endomorphism Torsion Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Torsion actions are natural, and a full level lets base-valued torsion points detect their equality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

theorem EndomorphismTorsionNaturality.constantGroupMap_ext_base {S : Scheme.{u}} {G H : Type v} [Group G] [Group H]
    {α β : Constant.GroupMaps.constantGroupFunctor S G ⟶ Constant.GroupMaps.constantGroupFunctor S H}
    (h : α.app (.op (Over.mk (𝟙 S))) = β.app (.op (Over.mk (𝟙 S)))) : α = β := by
  apply Constant.GroupMaps.constantGroupMap_ext
  intro s
  apply MonoidHom.ext
  intro g
  exact congrArg (fun a => LocallyConstant.toFun (a (LocallyConstant.const S g)) s) h

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.endRingTorsionNatural (n : ℕ) (f : A.EndRing) : A.torsionFunctor n ⟶ A.torsionFunctor n where
  app T := GrpCat.ofHom (A.endRingTorsionMap n T.unop f)
  naturality _ _ φ := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc φ.unop x.val f.toMul.hom.hom)

def Abelian.Schemes.AbelianScheme.fullLevelEndomorphismNatural {n : ℕ} (level : A.FullLevel n) (f : A.EndRing) :
    Constant.GroupMaps.constantGroupFunctor S (Multiplicative (Fin (2 * g) → ZMod n)) ⟶
      Constant.GroupMaps.constantGroupFunctor S (Multiplicative (Fin (2 * g) → ZMod n)) :=
  level.hom ≫ A.endRingTorsionNatural n f ≫ level.inv

theorem Abelian.Schemes.AbelianScheme.endRingTorsionNatural_eq_of_base {n : ℕ} (level : A.FullLevel n) (f k : A.EndRing)
    (h : A.endRingTorsionAction n (Over.mk (𝟙 S)) f =
      A.endRingTorsionAction n (Over.mk (𝟙 S)) k) :
    A.endRingTorsionNatural n f = A.endRingTorsionNatural n k := by
  have hb : (A.endRingTorsionNatural n f).app (.op (Over.mk (𝟙 S))) =
      (A.endRingTorsionNatural n k).app (.op (Over.mk (𝟙 S))) := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact congrArg (fun e : AddMonoid.End (Additive (A.torsionPoints n (Over.mk (𝟙 S)))) =>
      (e (Additive.ofMul x)).toMul) h
  have hc : A.fullLevelEndomorphismNatural level f = A.fullLevelEndomorphismNatural level k := by
    apply EndomorphismTorsionNaturality.constantGroupMap_ext_base
    change level.hom.app _ ≫ (A.endRingTorsionNatural n f).app _ ≫ level.inv.app _ =
      level.hom.app _ ≫ (A.endRingTorsionNatural n k).app _ ≫ level.inv.app _
    rw [hb]
  let e : Constant.GroupMaps.constantGroupFunctor S (Multiplicative (Fin (2 * g) → ZMod n)) ≅
      A.torsionFunctor n := level
  apply (cancel_epi e.hom).mp
  apply (cancel_mono e.inv).mp
  exact (Category.assoc e.hom (A.endRingTorsionNatural n f) e.inv).trans
    (hc.trans (Category.assoc e.hom (A.endRingTorsionNatural n k) e.inv).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
