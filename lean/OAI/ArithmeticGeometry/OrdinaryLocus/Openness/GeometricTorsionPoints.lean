import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenBaseChange
import Mathlib.Algebra.Field.ZMod

/-! # Geometric Torsion Points -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricTorsionPoints.Construction

noncomputable section

/-! Torsion points of geometric fibers and their characteristic. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- T-valued torsion points over S are rational torsion points of the base change to T. -/
theorem torsionPointCard_fieldBaseChange
    {S T : Scheme} (t : T ⟶ S) (A : Over S) [GrpObj A] (n : ℕ) :
    Nat.card {x : Over.mk (𝟙 T) ⟶ (Over.pullback t).obj A // x ^ n = 1} =
      Nat.card {x : Over.mk t ⟶ A // x ^ n = 1} := by
  let e₀ : (Over.map t).obj (Over.mk (𝟙 T)) ≅ Over.mk t :=
    Over.isoMk (Iso.refl T) (by simp)
  let e := (Iso.homCongr (Iso.refl (Over.mk (𝟙 T))) (BaseChange.Construction.torsionBaseChangeIso t A n).symm).trans
    (((Over.mapPullbackAdj t).homEquiv (Over.mk (𝟙 T)) (DefinitionsTorsion.Construction.torsionScheme A n)).symm.trans
      (Iso.homCongr e₀ (Iso.refl (DefinitionsTorsion.Construction.torsionScheme A n))))
  exact (Nat.card_congr (DefinitionsTorsion.Construction.torsionPointsEquiv ((Over.pullback t).obj A) n (Over.mk (𝟙 T)))).symm.trans
    ((Nat.card_congr e).trans (Nat.card_congr (DefinitionsTorsion.Construction.torsionPointsEquiv A n (Over.mk t))))

/-- A field admitting a map of spectra to Spec(Z/p) has characteristic p. -/
theorem charP_of_spec_to_ZMod
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K]
    (f : Spec (.of K) ⟶ Spec (.of (ZMod p))) : CharP K p := by
  let φ : ZMod p →+* K := (Spec.preimage f).hom
  exact charP_of_injective_ringHom φ.injective p

/-- The algebraically closed fields in Openness's geometric fibers have characteristic p. -/
theorem charP_geometric_residueField
    (p : ℕ) [Fact p.Prime] (S : Over (Spec (.of (ZMod p)))) (s : S.left) :
    CharP (AlgebraicClosure (S.left.residueField s)) p :=
  charP_of_spec_to_ZMod p ((DefinitionsTorsion.geometricPoint S.left s).hom ≫ S.hom)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricTorsionPoints.Construction
