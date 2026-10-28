import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieMem
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Lie
import OAI.NumberTheory.ArithmeticGroups.Lattices.MultilinearAction

/-! # Lie Bracket -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieBracket.Construction

noncomputable section

/-! The real Minkowski Lie bracket is an integral bilinear tensor and
is preserved by the actual archimedean adjoint representation. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing

theorem lieMixedSpan_commutator_mem
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    {A B : Matrix (Fin n) (Fin n) (mixedSpace k)}
    (hA : A ∈ Lie.MixedLattice.Construction.lieMixedSpan G) (hB : B ∈ Lie.MixedLattice.Construction.lieMixedSpan G) :
    A * B - B * A ∈ Lie.MixedLattice.Construction.lieMixedSpan G := by
  apply (LieEq.Construction.lieMixedModule_mem_iff_completions G hG _).mpr
  intro v
  have ha := (LieEq.Construction.lieMixedModule_mem_iff_completions G hG A).mp hA v
  have hb := (LieEq.Construction.lieMixedModule_mem_iff_completions G hG B).mp hB v
  change (QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix (A * B - B * A) ∈ _
  rw [map_sub, map_mul, map_mul]
  exact (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion))).lie_mem ha hb

def lieMixedBracket
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A B : Lie.MixedLattice.Construction.lieMixedSpan G) : Lie.MixedLattice.Construction.lieMixedSpan G :=
  ⟨A.val * B.val - B.val * A.val, lieMixedSpan_commutator_mem G hG A.property B.property⟩

theorem lieMixedBracket_integral
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A B : Lie.MixedLattice.Construction.lieMixedSpan G) (hA : A ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G) (hB : B ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G) :
    lieMixedBracket G hG A B ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G := by
  obtain ⟨a, ha, hea⟩ := hA
  obtain ⟨b, hb, heb⟩ := hB
  refine ⟨⁅a, b⁆, Integral.Lie.Construction.integralLieLattice_lie_mem G a b ha hb, ?_⟩
  change (mixedEmbedding k).mapMatrix (a.val * b.val - b.val * a.val) = A.val * B.val - B.val * A.val
  rw [map_sub, map_mul, map_mul]
  change Lie.MixedLattice.Construction.lieMixedEmbedding G a * Lie.MixedLattice.Construction.lieMixedEmbedding G b - Lie.MixedLattice.Construction.lieMixedEmbedding G b * Lie.MixedLattice.Construction.lieMixedEmbedding G a = _
  rw [hea, heb]
  rfl

def lieMixedBracketForm
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    MultilinearMap ℝ (fun _ : Fin 2 => Lie.MixedLattice.Construction.lieMixedSpan G) (Lie.MixedLattice.Construction.lieMixedSpan G) where
  toFun v := lieMixedBracket G hG (v 0) (v 1)
  map_update_add' v i x y := by
    apply Subtype.ext
    fin_cases i <;> simp [lieMixedBracket, Matrix.add_mul, Matrix.mul_add] <;> abel
  map_update_smul' v i c x := by
    apply Subtype.ext
    fin_cases i <;> simp [lieMixedBracket, smul_sub]

theorem archimedeanLieRepresentation_bracket
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (A B : Lie.MixedLattice.Construction.lieMixedSpan G) :
    Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG g (lieMixedBracket G hG A B) =
      lieMixedBracket G hG (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG g A)
        (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG g B) := by
  apply Subtype.ext
  change Archimedean.LieMem.Construction.matrixUnitConjugationEquiv (Archimedean.LieMem.Construction.archimedeanLieUnit G g) (A.val * B.val - B.val * A.val) =
    Archimedean.LieMem.Construction.matrixUnitConjugationEquiv (Archimedean.LieMem.Construction.archimedeanLieUnit G g) A.val *
      Archimedean.LieMem.Construction.matrixUnitConjugationEquiv (Archimedean.LieMem.Construction.archimedeanLieUnit G g) B.val -
    Archimedean.LieMem.Construction.matrixUnitConjugationEquiv (Archimedean.LieMem.Construction.archimedeanLieUnit G g) B.val *
      Archimedean.LieMem.Construction.matrixUnitConjugationEquiv (Archimedean.LieMem.Construction.archimedeanLieUnit G g) A.val
  exact (Matrix.lieConj (Archimedean.LieMem.Construction.archimedeanLieUnit G g).val (Archimedean.LieMem.Construction.archimedeanLieUnit G g).invertible).map_lie A.val B.val

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieBracket.Construction
