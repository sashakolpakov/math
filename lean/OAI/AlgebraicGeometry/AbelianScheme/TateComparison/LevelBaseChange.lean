import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Level Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LevelBaseChange

noncomputable section

/-! Full-level preservation is the identity on every torsion test point.
It is preserved by arbitrary base change and reflected by faithful
pullback, including the field extensions used in PEL rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover
variable {S T : Scheme} {g N : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem preservesFullLevel_iff_all_torsion (α : A.FullLevel N) (f : A.scheme ⟶ A.scheme) :
    AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.PreservesFullLevel α f ↔
      ∀ (U : Over S) (x : U ⟶ A.scheme), x ^ N = 1 → x ≫ f = x := by
  constructor
  · intro h U x hx
    obtain ⟨c, hc⟩ := (α.app (.op U)).groupIsoToMulEquiv.surjective
      (⟨x, hx⟩ : A.torsionPoints N U)
    exact (congrArg (fun y : A.torsionPoints N U => y.val ≫ f) hc).symm.trans
      ((h U c).trans (congrArg Subtype.val hc))
  · intro h U c
    exact h U (α.hom.app (.op U) c).val (α.hom.app (.op U) c).property

theorem preservesFullLevel_pullback (α : A.FullLevel N) (f : A.scheme ⟶ A.scheme)
    (b : T ⟶ S) (h : AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.PreservesFullLevel α f) :
    AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.PreservesFullLevel (α.pullback b) ((Over.pullback b).map f) := by
  apply (preservesFullLevel_iff_all_torsion (A.pullback b) (α.pullback b) _).mpr
  intro U x hx
  apply (A.baseChangePointsEquiv b U).injective
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map]
  apply (preservesFullLevel_iff_all_torsion A α f).mp h
  change (A.baseChangePointsMulEquiv b U x) ^ N = 1
  rw [← map_pow, hx, map_one]

theorem preservesFullLevel_of_pullback (α : A.FullLevel N) (f : A.scheme ⟶ A.scheme)
    (b : T ⟶ S) [(Over.pullback b).Faithful]
    (h : AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.PreservesFullLevel (α.pullback b) ((Over.pullback b).map f)) :
    AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover.PreservesFullLevel α f := by
  apply (preservesFullLevel_iff_all_torsion A α f).mpr
  intro U x hx
  apply (Over.pullback b).map_injective
  rw [Functor.map_comp]
  apply (preservesFullLevel_iff_all_torsion (A.pullback b) (α.pullback b) _).mp h
  exact ((map_pow (Over.pullback b).homMonoidHom x N).symm.trans
    (congrArg (Over.pullback b).map hx)).trans (Over.pullback b).map_one

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LevelBaseChange
