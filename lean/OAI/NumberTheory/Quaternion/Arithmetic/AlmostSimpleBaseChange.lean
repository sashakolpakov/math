import OAI.NumberTheory.Quaternion.Arithmetic.GeometricPointTopology
import OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicHypotheses

/-! # Almost Simple Base Change -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleBaseChange

noncomputable section

/-! Transfer the specified geometric almost-simple condition to rational
points of the geometric base change, preserving the Zariski topology. -/

open scoped Classical
open Set

variable {k : Type} [Field k] {n : ℕ}

theorem geometricBaseChange_almostSimple_normals
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n) (hG : AlgebraicHypotheses.IsAbsolutelyAlmostSimple G)
    (N : Subgroup (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))).RationalPoints)
    (hN : N.Normal)
    (hclosed : @IsClosed _
      (ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))) N)
    (hconnected : @IsConnected _
      (ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k)))) N) :
    N = ⊥ ∨ N = ⊤ := by
  let H := ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))
  let : TopologicalSpace H.RationalPoints := ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology H
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let e := GeometricPointTopology.geometricBaseChangePointEquiv G
  let eh := GeometricPointTopology.geometricBaseChangePointHomeomorph G
  let M := N.map e.toMonoidHom
  have hMN : M.Normal := Subgroup.Normal.map hN e.toMonoidHom e.surjective
  have hMC : IsClosed (M : Set G.GeometricPoints) := eh.isClosedMap _ hclosed
  have hMconn : IsConnected (M : Set G.GeometricPoints) :=
    hconnected.image eh eh.continuous.continuousOn
  rcases hG.2.2 M hMN hMC hMconn with hbot | htop
  · left
    apply le_antisymm _ bot_le
    intro g hg
    have he : e g ∈ M := ⟨g, hg, rfl⟩
    rw [hbot, Subgroup.mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  · right
    apply le_antisymm le_top
    intro g _
    have he : e g ∈ M := by rw [htop]; trivial
    obtain ⟨a, ha, he⟩ := he
    exact e.injective he ▸ ha

end

end OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleBaseChange
