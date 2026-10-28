import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.UnitSubgroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms

/-! # Preserving Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A level-preserving automorphism determines a unit acting identically on torsion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}

def Moduli.Isomorphisms.LevelPreservingIso.endRingUnit (e : Moduli.Isomorphisms.LevelPreservingIso A A) : A.abelian.EndRingˣ :=
  A.abelian.endRingUnitOfIso e.abelian

theorem Moduli.Isomorphisms.LevelPreservingIso.torsionAction_eq_one (e : Moduli.Isomorphisms.LevelPreservingIso A A) (T : Over S) :
    A.abelian.endRingTorsionAction N T e.endRingUnit.val = 1 := by
  apply AddMonoidHom.ext
  intro x
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change x.toMul.val ≫ e.abelian.hom = x.toMul.val
  let l := (A.level.app (.op T)).groupIsoToMulEquiv
  have hx : (A.level.hom.app (.op T) (l.symm x.toMul)).val = x.toMul.val :=
    congrArg (fun y : A.abelian.torsionPoints N T => y.val) (l.apply_symm_apply x.toMul)
  exact (congrArg (fun a => a ≫ e.abelian.hom) hx.symm).trans
    ((e.level T (l.symm x.toMul)).trans hx)

def Moduli.Isomorphisms.LevelPreservingIso.levelUnit (e : Moduli.Isomorphisms.LevelPreservingIso A A) : A.abelian.levelUnitSubgroup N :=
  ⟨e.endRingUnit, (A.abelian.mem_levelUnitSubgroup_iff N e.endRingUnit).mpr
    (e.torsionAction_eq_one (Over.mk (𝟙 S)))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
