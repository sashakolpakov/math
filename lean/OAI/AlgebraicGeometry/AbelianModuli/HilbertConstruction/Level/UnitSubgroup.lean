import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PointGroups
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TorsionDetection
import Mathlib.GroupTheory.Index

/-! # Unit Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The subgroup of automorphisms acting trivially on full-level torsion has finite index over a field. Its torsion-freeness is not asserted here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.torsionUnitAction (n : ℕ) (T : Over S) :
    A.EndRingˣ →* (AddMonoid.End (Additive (A.torsionPoints n T)))ˣ :=
  Units.map (A.endRingTorsionAction n T).toMonoidHom

def Abelian.Schemes.AbelianScheme.levelUnitSubgroup (n : ℕ) : Subgroup A.EndRingˣ :=
  (A.torsionUnitAction n (Over.mk (𝟙 S))).ker

theorem Abelian.Schemes.AbelianScheme.mem_levelUnitSubgroup_iff (n : ℕ) (v : A.EndRingˣ) :
    v ∈ A.levelUnitSubgroup n ↔ A.endRingTorsionAction n (Over.mk (𝟙 S)) v.val = 1 := by
  change A.torsionUnitAction n (Over.mk (𝟙 S)) v = 1 ↔ _
  exact Units.ext_iff

theorem Abelian.Schemes.AbelianScheme.levelUnitSubgroup_torsionMap {n : ℕ} (level : A.FullLevel n)
    (v : A.levelUnitSubgroup n) :
    Abelian.Schemes.AbelianScheme.torsionMap n v.val.val.toMul.hom.hom = 𝟙 (A.torsionScheme n) :=
  A.torsionMap_eq_id_of_baseAction level v.val.val
    ((A.mem_levelUnitSubgroup_iff n v.val).mp v.property)

theorem Abelian.Schemes.AbelianScheme.levelUnitSubgroup_finiteIndex {K : Type u} [Field K]
    (B : Abelian.Schemes.AbelianScheme g (Spec (.of K))) {n : ℕ} [NeZero n] (level : B.FullLevel n) :
    (B.levelUnitSubgroup n).FiniteIndex := by
  have := B.fullLevelTorsionEnd_finite level
  exact Subgroup.finiteIndex_ker (B.torsionUnitAction n (Over.mk (𝟙 (Spec (.of K)))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
