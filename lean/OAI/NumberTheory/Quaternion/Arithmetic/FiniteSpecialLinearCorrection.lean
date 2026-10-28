import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison
import OAI.NumberTheory.Quaternion.Arithmetic.SpecialLinearAdeles

/-! # Finite Special Linear Correction -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteSpecialLinearCorrection

noncomputable section

/-! Strong approximation for the ambient special-linear group gives
rational integral corrections for arbitrary determinant-one adelic matrices. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

instance finiteAdelicGroupTopologicalGroup (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    IsTopologicalGroup (FiniteAdelicMatrices.FiniteAdelicGroupPoints G) := by
  let : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (LocalAdeles.integralLocalSubgroup G (.inr v) : Set (LocalAdeles.LocalPoints G (.inr v)))) :=
    ⟨fun v => LocalAdeles.integralLocalSubgroup_isOpen G (.inr v)⟩
  exact inferInstance

def integralFiniteAdelicSubgroup (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) : Subgroup (FiniteAdelicMatrices.FiniteAdelicGroupPoints G) where
  carrier := {g | ∀ v, g v ∈ LocalAdeles.integralLocalSubgroup G (.inr v)}
  one_mem' v := (LocalAdeles.integralLocalSubgroup G (.inr v)).one_mem
  mul_mem' hg hh v := (LocalAdeles.integralLocalSubgroup G (.inr v)).mul_mem (hg v) (hh v)
  inv_mem' hg v := (LocalAdeles.integralLocalSubgroup G (.inr v)).inv_mem (hg v)

theorem integralFiniteAdelicSubgroup_isOpen (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    IsOpen (integralFiniteAdelicSubgroup G : Set (FiniteAdelicMatrices.FiniteAdelicGroupPoints G)) :=
  RestrictedProduct.isOpen_forall_mem (fun v : HeightOneSpectrum (𝓞 F) =>
    LocalAdeles.integralLocalSubgroup_isOpen G (.inr v))

theorem finiteAdelicMatrix_integral_iff (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) :
    g ∈ integralFiniteAdelicSubgroup G ↔
      (∀ i j, FiniteAdelicMatrices.finiteAdelicMatrix G g i j ∈ ScalarApproximation.integralScalarAdeles F) ∧
      (∀ i j, FiniteAdelicMatrices.finiteAdelicMatrix G g⁻¹ i j ∈ ScalarApproximation.integralScalarAdeles F) := by
  constructor
  · intro h
    exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩
  · rintro ⟨h, hi⟩ v
    exact ⟨fun i j => h i j v, fun i j => hi i j v⟩

def finiteAdelicToSpecialLinear (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) :
    FiniteAdelicMatrices.FiniteAdelicGroupPoints (SpecialLinearAdeles.specialLinearMatrixGroup F n) :=
  ⟨fun v => ⟨(g v).val, Subgroup.mem_top _⟩, by
    filter_upwards [g.property] with v hv
    exact hv⟩

theorem finiteAdelicToSpecialLinear_matrix (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) :
    FiniteAdelicMatrices.finiteAdelicMatrix (SpecialLinearAdeles.specialLinearMatrixGroup F n) (finiteAdelicToSpecialLinear G g) =
      FiniteAdelicMatrices.finiteAdelicMatrix G g := rfl

theorem denseRange_finiteSpecialLinearDiagonal [Nontrivial (Fin n)] :
    DenseRange (FiniteAdelicComparison.diagonalFiniteAdelic (SpecialLinearAdeles.specialLinearMatrixGroup F n)) :=
  FiniteAdelicComparison.denseRange_diagonalFiniteAdelic_of_away _
    (SpecialLinearAdeles.strongApproximation_specialLinear FiniteAdelicComparison.allArchimedeanPlaces FiniteAdelicComparison.mem_allArchimedeanPlaces)

theorem finiteSpecialLinear_integral_correction [Nontrivial (Fin n)]
    (a : FiniteAdelicMatrices.FiniteAdelicGroupPoints (SpecialLinearAdeles.specialLinearMatrixGroup F n)) :
    ∃ b : (SpecialLinearAdeles.specialLinearMatrixGroup F n).RationalPoints,
      a * FiniteAdelicComparison.diagonalFiniteAdelic (SpecialLinearAdeles.specialLinearMatrixGroup F n) b ∈
        integralFiniteAdelicSubgroup (SpecialLinearAdeles.specialLinearMatrixGroup F n) := by
  let G := SpecialLinearAdeles.specialLinearMatrixGroup F n
  have ho : IsOpen {g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G | a * g ∈ integralFiniteAdelicSubgroup G} :=
    (integralFiniteAdelicSubgroup_isOpen G).preimage (continuous_const_mul a)
  have hn : {g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G | a * g ∈ integralFiniteAdelicSubgroup G}.Nonempty := by
    refine ⟨a⁻¹, ?_⟩
    change a * a⁻¹ ∈ integralFiniteAdelicSubgroup G
    rw [mul_inv_cancel]
    exact (integralFiniteAdelicSubgroup G).one_mem
  exact denseRange_finiteSpecialLinearDiagonal.exists_mem_open ho hn

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteSpecialLinearCorrection
