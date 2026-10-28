import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismTorsionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionFunctoriality

/-! # Torsion Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Under full level, the action on base-valued torsion points determines the map of torsion schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g n : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.torsionMap_eq_of_baseAction (level : A.FullLevel n) (f k : A.EndRing)
    (h : A.endRingTorsionAction n (Over.mk (𝟙 S)) f =
      A.endRingTorsionAction n (Over.mk (𝟙 S)) k) :
    Abelian.Schemes.AbelianScheme.torsionMap n f.toMul.hom.hom = Abelian.Schemes.AbelianScheme.torsionMap n k.toMul.hom.hom := by
  have hn := A.endRingTorsionNatural_eq_of_base level f k h
  let x : A.torsionPoints n (A.torsionScheme n) :=
    ⟨A.torsionInclusion n, A.torsionInclusion_pow n⟩
  have he := congrArg (fun α : A.torsionFunctor n ⟶ A.torsionFunctor n =>
    (α.app (.op (A.torsionScheme n)) x).val) hn
  apply (cancel_mono (A.torsionInclusion n)).mp
  rw [Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion, Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion]
  exact he

theorem Abelian.Schemes.AbelianScheme.torsionMap_eq_id_of_baseAction (level : A.FullLevel n) (f : A.EndRing)
    (h : A.endRingTorsionAction n (Over.mk (𝟙 S)) f = 1) :
    Abelian.Schemes.AbelianScheme.torsionMap n f.toMul.hom.hom = 𝟙 (A.torsionScheme n) := by
  have he := A.torsionMap_eq_of_baseAction level f 1
    (h.trans (A.endRingTorsionAction n (Over.mk (𝟙 S))).map_one.symm)
  exact he.trans (Abelian.Schemes.AbelianScheme.torsionMap_id A n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
