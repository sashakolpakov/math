import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieBracket
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Lie
import OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicAdjointNilpotents

/-! # Adjoint Operator -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.AdjointOperator.Construction

noncomputable section

/-! Intrinsic adjoint operators on the real Minkowski Lie algebra,
with faithful rational compatibility and no nonzero nilpotent lattice elements. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing

def lieMixedAdjoint
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A : Lie.MixedLattice.Construction.lieMixedSpan G) : Module.End ℝ (Lie.MixedLattice.Construction.lieMixedSpan G) where
  toFun B := LieBracket.Construction.lieMixedBracket G hG A B
  map_add' B C := by
    apply Subtype.ext
    simp [LieBracket.Construction.lieMixedBracket, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c B := by
    apply Subtype.ext
    simp [LieBracket.Construction.lieMixedBracket, smul_sub]

def lieMixedAdjointLinear
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    Lie.MixedLattice.Construction.lieMixedSpan G →ₗ[ℝ] Module.End ℝ (Lie.MixedLattice.Construction.lieMixedSpan G) where
  toFun := lieMixedAdjoint G hG
  map_add' A B := by
    apply LinearMap.ext
    intro C
    apply Subtype.ext
    simp [lieMixedAdjoint, LieBracket.Construction.lieMixedBracket, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c A := by
    apply LinearMap.ext
    intro B
    apply Subtype.ext
    simp [lieMixedAdjoint, LieBracket.Construction.lieMixedBracket, smul_sub]

theorem lieMixedSpanRationalMap_injective
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Function.Injective (Archimedean.Lie.Construction.lieMixedSpanRationalMap G) := by
  intro A B h
  apply Subtype.ext
  ext i j : 1
  have he := congrArg (fun X : Lie.MixedLattice.Construction.lieMixedSpan G => X.val i j) h
  exact (mixedEmbedding k).injective he

theorem lieMixedAdjoint_rational
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A B : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    lieMixedAdjoint G hG (Archimedean.Lie.Construction.lieMixedSpanRationalMap G A) (Archimedean.Lie.Construction.lieMixedSpanRationalMap G B) =
      Archimedean.Lie.Construction.lieMixedSpanRationalMap G (LieAlgebra.ad k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) A B) := by
  apply Subtype.ext
  change (mixedEmbedding k).mapMatrix A.val * (mixedEmbedding k).mapMatrix B.val -
      (mixedEmbedding k).mapMatrix B.val * (mixedEmbedding k).mapMatrix A.val =
    (mixedEmbedding k).mapMatrix (A.val * B.val - B.val * A.val)
  rw [map_sub, map_mul, map_mul]

theorem lieMixedAdjoint_pow_rational
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A B : Infinitesimal.Action.Construction.infinitesimalStabilizer G) (r : ℕ) :
    (lieMixedAdjoint G hG (Archimedean.Lie.Construction.lieMixedSpanRationalMap G A) ^ r) (Archimedean.Lie.Construction.lieMixedSpanRationalMap G B) =
      Archimedean.Lie.Construction.lieMixedSpanRationalMap G ((LieAlgebra.ad k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) A ^ r) B) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih,
        lieMixedAdjoint_rational]

theorem anisotropic_lieMixedAdjoint_nilpotent_lattice_eq_zero
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) (A : Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup)
    (hA : A ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup)
    (hnil : IsNilpotent (lieMixedAdjoint G.matrixGroup G.connected A)) : A = 0 := by
  obtain ⟨a, _, hea⟩ := hA
  have he : Archimedean.Lie.Construction.lieMixedSpanRationalMap G.matrixGroup a = A := Subtype.ext hea
  have ha : IsNilpotent (LieAlgebra.ad k (Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup) a) := by
    obtain ⟨r, hr⟩ := hnil
    refine ⟨r, ?_⟩
    apply LinearMap.ext
    intro b
    apply lieMixedSpanRationalMap_injective G.matrixGroup
    rw [LinearMap.zero_apply, map_zero,
      ← lieMixedAdjoint_pow_rational G.matrixGroup G.connected a b r, he, hr]
    rfl
  have ha0 := AnisotropicAdjointNilpotents.Construction.anisotropic_infinitesimal_ad_nilpotent_eq_zero G haniso a ha
  rw [← he, ha0, map_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.AdjointOperator.Construction
