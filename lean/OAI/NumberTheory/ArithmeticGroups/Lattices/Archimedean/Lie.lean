import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieMem
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Lie
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction

/-! # Lie -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Lie.Construction

noncomputable section

/-! The rational adjoint action agrees with its Minkowski realization,
and the actual standard arithmetic subgroup preserves the Lie lattice. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

def lieMixedSpanRationalMap
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Infinitesimal.Action.Construction.infinitesimalStabilizer G →ₗ[ℚ] Lie.MixedLattice.Construction.lieMixedSpan G where
  toFun A := ⟨Lie.MixedLattice.Construction.lieMixedEmbedding G A, Lie.MixedLattice.Construction.lieMixedEmbedding_mem_span G A⟩
  map_add' A B := Subtype.ext ((Lie.MixedLattice.Construction.lieMixedRationalMap G).map_add A B)
  map_smul' q A := Subtype.ext ((Lie.MixedLattice.Construction.lieMixedRationalMap G).map_smul q A)

theorem archimedeanLieUnit_diagonal
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints) :
    LieMem.Construction.archimedeanLieUnit G (Quotient.Construction.fullArchimedeanRationalPointMap G g) =
      (Matrix.SpecialLinearGroup.map (mixedEmbedding k) g.val).toGL := by
  change (Quotient.Construction.archimedeanMixedSL k n (ExteriorAction.Construction.fullArchimedeanSLMap k n g.val)).toGL = _
  rw [Minkowski.IntegralAction.Construction.archimedeanMixedSL_diagonal]

theorem archimedeanLieRepresentation_diagonal
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : G.RationalPoints) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    LieMem.Construction.archimedeanLieRepresentation G hG (Quotient.Construction.fullArchimedeanRationalPointMap G g)
        (lieMixedSpanRationalMap G A) =
      lieMixedSpanRationalMap G (ExponentialNormal.Construction.infinitesimalAdjoint G g A) := by
  apply Subtype.ext
  change (LieMem.Construction.archimedeanLieEquiv G hG (Quotient.Construction.fullArchimedeanRationalPointMap G g)
    (lieMixedSpanRationalMap G A)).val = _
  rw [LieMem.Construction.archimedeanLieEquiv_apply, archimedeanLieUnit_diagonal]
  rw [← map_inv Matrix.SpecialLinearGroup.toGL,
    ← map_inv (Matrix.SpecialLinearGroup.map (mixedEmbedding k))]
  change (mixedEmbedding k).mapMatrix (g.val : Matrix (Fin n) (Fin n) k) *
      (mixedEmbedding k).mapMatrix A.val *
      (mixedEmbedding k).mapMatrix ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) =
    (mixedEmbedding k).mapMatrix (ExponentialNormal.Construction.infinitesimalAdjoint G g A).val
  rw [ExponentialNormal.Construction.infinitesimalAdjoint_apply, map_mul, map_mul]

theorem standard_arithmetic_archimedeanLie_preserves_lattice
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : G.RationalPoints) (hg : g ∈ G.latticeStabilizer (IntegralLattice.FullLattice.standard k n))
    (x : Lie.MixedLattice.Construction.lieMixedSpan G) (hx : x ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G) :
    LieMem.Construction.archimedeanLieRepresentation G hG (Quotient.Construction.fullArchimedeanRationalPointMap G g) x ∈
      Lie.MixedLattice.Construction.lieMixedLatticeInSpan G := by
  obtain ⟨A, hA, hAx⟩ := hx
  have he : lieMixedSpanRationalMap G A = x := Subtype.ext hAx
  rw [← he, archimedeanLieRepresentation_diagonal]
  exact ⟨ExponentialNormal.Construction.infinitesimalAdjoint G g A,
    Integral.Lie.Construction.standard_arithmetic_adjoint_preserves_integralLieLattice G g hg A hA, rfl⟩

theorem standard_arithmetic_archimedeanLie_lattice_iff
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : G.RationalPoints) (hg : g ∈ G.latticeStabilizer (IntegralLattice.FullLattice.standard k n))
    (x : Lie.MixedLattice.Construction.lieMixedSpan G) :
    LieMem.Construction.archimedeanLieRepresentation G hG (Quotient.Construction.fullArchimedeanRationalPointMap G g) x ∈
        Lie.MixedLattice.Construction.lieMixedLatticeInSpan G ↔ x ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G := by
  constructor
  · intro hx
    have hi := standard_arithmetic_archimedeanLie_preserves_lattice G hG g⁻¹
      ((G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).inv_mem hg) _ hx
    rw [map_inv, map_inv] at hi
    change (LieMem.Construction.archimedeanLieRepresentation G hG (Quotient.Construction.fullArchimedeanRationalPointMap G g)).symm
      ((LieMem.Construction.archimedeanLieRepresentation G hG (Quotient.Construction.fullArchimedeanRationalPointMap G g)) x) ∈ _ at hi
    rw [LinearEquiv.symm_apply_apply] at hi
    exact hi
  · exact standard_arithmetic_archimedeanLie_preserves_lattice G hG g hg x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Lie.Construction
