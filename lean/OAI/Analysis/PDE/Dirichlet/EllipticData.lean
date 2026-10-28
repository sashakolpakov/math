import OAI.Analysis.PDE.Dirichlet.PositiveDeterminant
import OAI.Analysis.PDE.Dirichlet.NormalBounded
import OAI.Analysis.PDE.Dirichlet.Coercivity

open Set Metric
open scoped Matrix ComplexOrder MatrixOrder Topology Matrix.Norms.Elementwise

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

def boundedPositiveData (n : ℕ) (R m : ℝ) : Set (Matrix (Fin n) (Fin n) Q) :=
  {A | ‖A‖ ≤ R ∧ A.IsHermitian ∧ (∀ z, 0 ≤ (quaternionForm A z).re) ∧ m ≤ OAI.LinearAlgebra.Moore.mooreDet n A}

theorem isCompact_boundedPositiveData (n : ℕ) (R m : ℝ) :
    IsCompact (boundedPositiveData n R m) := by
  apply (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) Q) R).of_isClosed_subset
  · have hHerm : IsClosed {A : Matrix (Fin n) (Fin n) Q | A.IsHermitian} :=
      isClosed_eq (by fun_prop) continuous_id
    have hq : IsClosed {A : Matrix (Fin n) (Fin n) Q | ∀ z, 0 ≤ (quaternionForm A z).re} := by
      have heq : {A : Matrix (Fin n) (Fin n) Q | ∀ z, 0 ≤ (quaternionForm A z).re} =
          ⋂ z : Fin n → Q, {A | 0 ≤ (quaternionForm A z).re} := by
        ext A
        simp
      rw [heq]
      exact isClosed_iInter (fun z ↦ isClosed_le continuous_const
        (continuous_quaternionForm_re continuous_id continuous_const))
    exact (isClosed_le continuous_norm continuous_const).inter
      (hHerm.inter (hq.inter (isClosed_le continuous_const (OAI.LinearAlgebra.Moore.continuous_mooreDet n))))
  · intro A hA
    simpa only [mem_closedBall, dist_zero_right] using hA.1

theorem boundedPositiveData_posDef {n : ℕ} {R m : ℝ} (hm : 0 < m)
    {A : Matrix (Fin n) (Fin n) Q} (hA : A ∈ boundedPositiveData n R m) :
    (OAI.LinearAlgebra.Moore.complexify A).PosDef := by
  exact complexify_posDef_of_posSemidef_mooreDet_pos A
    ((OAI.LinearAlgebra.Moore.complexify_posSemidef_iff hA.2.1).mpr hA.2.2.1) (hm.trans_le hA.2.2.2)

theorem outer_real_smul {n : ℕ} (a : ℝ) (g : Fin n → Q) :
    OAI.Analysis.Calculus.Quaternion.outer (a • g) = a ^ 2 • OAI.Analysis.Calculus.Quaternion.outer g := by
  apply Matrix.ext
  intro i j
  simp [OAI.Analysis.Calculus.Quaternion.outer, Pi.smul_apply, smul_smul, pow_two]

/-- The exact real rank-one symbol of log det H. -/
def logPrincipalSymbol {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (v : CoordinateSpace n 4) : ℝ :=
  OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v)) / OAI.LinearAlgebra.Moore.mooreDet n A

theorem logPrincipalSymbol_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (a : ℝ) (v : CoordinateSpace n 4) :
    logPrincipalSymbol A (a • v) = a ^ 2 * logPrincipalSymbol A v := by
  unfold logPrincipalSymbol
  rw [gradientMap_real_smul, outer_real_smul, OAI.LinearAlgebra.Moore.mooreDifferential_smul]
  ring

theorem logPrincipalSymbol_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (v : CoordinateSpace n 4) (hv : v ≠ 0) :
    0 < logPrincipalSymbol A v := by
  have hd := OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef A hA
  obtain ⟨C, hAC, hCA⟩ := OAI.LinearAlgebra.Moore.exists_quaternion_inverse_of_complexify_posDef A hA
  apply div_pos _ hd
  apply mooreDifferential_outer_pos A C _ hA hAC hCA hd
  intro hz
  have hzero : OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (0 : Fin n × Fin 4 → ℝ) = 0 := by
    funext i
    simp [OAI.Analysis.Calculus.Quaternion.gradientMap]
  have heq := OAI.Analysis.Calculus.Quaternion.gradientMap_fourSlots_injective (hz.trans hzero.symm)
  apply hv
  ext i
  exact congrFun heq i

theorem continuousOn_logPrincipalSymbol {n : ℕ} {R m : ℝ} (hm : 0 < m) :
    ContinuousOn (fun p : Matrix (Fin n) (Fin n) Q × CoordinateSpace n 4 ↦
      logPrincipalSymbol p.1 p.2) (boundedPositiveData n R m ×ˢ sphere 0 1) := by
  have hg : Continuous (fun p : Matrix (Fin n) (Fin n) Q × CoordinateSpace n 4 ↦
      OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots p.2) := by
    unfold OAI.Analysis.Calculus.Quaternion.gradientMap
    fun_prop
  have ho : Continuous (fun p : Matrix (Fin n) (Fin n) Q × CoordinateSpace n 4 ↦
      OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots p.2)) :=
    continuous_outer_map (n := n) (ν := fun p : Matrix (Fin n) (Fin n) Q × CoordinateSpace n 4 ↦
      OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots p.2) hg
  have hp : Continuous (fun p : Matrix (Fin n) (Fin n) Q × CoordinateSpace n 4 ↦
      (p.1, OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots p.2))) := continuous_fst.prodMk ho
  have hn : Continuous (fun p : Matrix (Fin n) (Fin n) Q × CoordinateSpace n 4 ↦
      OAI.LinearAlgebra.Moore.mooreDifferential n p.1 (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots p.2))) :=
    (OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).comp
      (f := fun p : Matrix (Fin n) (Fin n) Q × CoordinateSpace n 4 ↦
        (p.1, OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots p.2))) hp
  exact hn.continuousOn.div ((OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp continuous_fst).continuousOn
    (fun p hp ↦ (hm.trans_le hp.1.2.2.2).ne')

/-- Norm and determinant bounds imply two-sided uniform real ellipticity,
independently of the particular matrix or solution. -/
theorem logPrincipalSymbol_uniform_of_bounded_data {n : ℕ} (hn : 1 ≤ n)
    (R m : ℝ) (hm : 0 < m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ A ∈ boundedPositiveData n R m,
      ∀ v : CoordinateSpace n 4, c * ‖v‖ ^ 2 ≤ logPrincipalSymbol A v ∧
        logPrincipalSymbol A v ≤ C * ‖v‖ ^ 2 := by
  by_cases hne : (boundedPositiveData n R m).Nonempty
  · have hK := isCompact_boundedPositiveData n R m
    have hq := continuousOn_logPrincipalSymbol (n := n) (R := R) hm
    have hs : ∀ A ∈ boundedPositiveData n R m, ∀ (a : ℝ) v,
        logPrincipalSymbol A (a • v) = a ^ 2 * logPrincipalSymbol A v :=
      fun A _ a v ↦ logPrincipalSymbol_smul A a v
    obtain ⟨c, hc, hlo⟩ := uniform_positive_quadratic_lower hK hne
      (fourSlot_unitSphere_nonempty hn) logPrincipalSymbol hq
      (fun A hA v hv ↦ logPrincipalSymbol_pos A (boundedPositiveData_posDef hm hA) v hv) hs
    obtain ⟨C, hC, hhi⟩ := uniform_quadratic_upper hK hne
      (fourSlot_unitSphere_nonempty hn) logPrincipalSymbol hq hs
    exact ⟨c, C, hc, hC, fun A hA v ↦ ⟨hlo A hA v, hhi A hA v⟩⟩
  · exact ⟨1, 1, zero_lt_one, zero_lt_one, fun A hA ↦ (hne ⟨A, hA⟩).elim⟩

end OAI.Analysis.PDE.Dirichlet
