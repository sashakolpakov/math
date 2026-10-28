import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices

/-! # Adelic Lattice Local Coordinates -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeLocalCoordinates

noncomputable section

/-! Local coordinate tests for the rational lattice attached to an
actual finite-adelic matrix group point. -/

open scoped Classical _root_.NumberField _root_.Matrix
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem finiteAdelicMatrix_mulVec_eval (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (x : Fin n → F) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) :
    FiniteAdelicMatrices.scalarFiniteAdeleEvaluation v ((FiniteAdelicMatrices.finiteAdelicMatrix G g *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) i) =
      ((g v).val.val *ᵥ (fun j => LocalAdeles.localEmbedding (.inr v) (x j))) i := by
  have he := RingHom.map_mulVec (FiniteAdelicMatrices.scalarFiniteAdeleEvaluation v) (FiniteAdelicMatrices.finiteAdelicMatrix G g)
    (FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) i
  have hM : (FiniteAdelicMatrices.finiteAdelicMatrix G g).map (FiniteAdelicMatrices.scalarFiniteAdeleEvaluation v) = (g v).val.val := rfl
  rw [hM] at he
  exact he

theorem finiteAdelicGroupLattice_mem_iff (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (x : Fin n → F) :
    x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g) ↔
      ∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
        ((g v).val.val *ᵥ (fun j => LocalAdeles.localEmbedding (.inr v) (x j))) i ∈ LocalAdeles.localIntegerRing (.inr v) := by
  constructor
  · intro hx v i
    have hi := (FiniteAdelicLattice.mem_finiteAdelicMatrixLattice _ x).mp hx i v
    exact (finiteAdelicMatrix_mulVec_eval G g x v i) ▸ hi
  · intro hx
    apply (FiniteAdelicLattice.mem_finiteAdelicMatrixLattice _ x).mpr
    intro i v
    exact (finiteAdelicMatrix_mulVec_eval G g x v i).symm ▸ hx v i

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeLocalCoordinates
