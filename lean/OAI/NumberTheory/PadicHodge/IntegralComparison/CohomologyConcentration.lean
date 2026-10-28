import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Cohomology Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration

noncomputable section

/-! A complex with cohomology in one degree is linked, by the canonical
truncation maps, to its genuine cohomology object in that degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

def zeroCyclesMap (K : CochainComplex C ℕ) :
    (CochainComplex.single₀ C).obj (K.cycles 0) ⟶ K :=
  (CochainComplex.fromSingle₀Equiv K (K.cycles 0)).symm
    ⟨K.iCycles 0, K.iCycles_d 0 1⟩

@[simp] theorem zeroCyclesMap_f_zero (K : CochainComplex C ℕ) :
    (zeroCyclesMap K).f 0 = K.iCycles 0 :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

theorem zeroCyclesMap_quasiIsoAt (K : CochainComplex C ℕ) :
    QuasiIsoAt (zeroCyclesMap K) 0 := by
  let A := (CochainComplex.single₀ C).obj (K.cycles 0)
  have hc : HomologicalComplex.cyclesMap (zeroCyclesMap K) 0 = A.iCycles 0 := by
    apply (cancel_mono (K.iCycles 0)).mp
    rw [HomologicalComplex.cyclesMap_i, zeroCyclesMap_f_zero]
  have : IsIso (A.iCycles 0) := A.isIso_iCycles 0 1 (by simp) (by simp [A])
  have : IsIso (HomologicalComplex.cyclesMap (zeroCyclesMap K) 0) := hc.symm ▸ inferInstance
  have h : IsIso (A.homologyπ 0 ≫ HomologicalComplex.homologyMap (zeroCyclesMap K) 0) := by
    rw [HomologicalComplex.homologyπ_naturality]
    infer_instance
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact IsIso.of_isIso_comp_left (A.homologyπ 0) _

theorem zeroCyclesMap_quasiIso (K : CochainComplex C ℕ)
    (hK : ∀ q, K.ExactAt (q + 1)) : QuasiIso (zeroCyclesMap K) := by
  constructor
  intro q
  cases q with
  | zero => exact zeroCyclesMap_quasiIsoAt K
  | succ q =>
    exact (quasiIsoAt_iff_exactAt' (zeroCyclesMap K) (q + 1) (hK q)).mpr
      (HomologicalComplex.exactAt_single_obj (.up ℕ) 0 _ (q + 1) (by omega))

abbrev shift (c : ℕ) : (ComplexShape.up ℕ).Embedding (.up ℕ) :=
  ComplexShape.embeddingUp'Add 1 c

abbrev tail (K : CochainComplex C ℕ) (c : ℕ) : CochainComplex C ℕ := K.truncGE' (shift c)

abbrev truncation (K : CochainComplex C ℕ) (c : ℕ) : CochainComplex C ℕ := K.truncGE (shift c)

def projection (K : CochainComplex C ℕ) (c : ℕ) : K ⟶ truncation K c := K.πTruncGE (shift c)

def cyclesHomologyIso (K : CochainComplex C ℕ) (c : ℕ) :
    (tail K c).cycles 0 ≅ K.homology c := by
  have h : (shift c).f 0 = c := by simp [shift]
  have : QuasiIsoAt (projection K c) c := K.quasiIsoAt_πTruncGE (shift c) h
  exact (tail K c).isoHomologyπ₀ ≪≫ ((tail K c).extendHomologyIso (shift c) h).symm ≪≫
    (isoOfQuasiIsoAt (projection K c) c).symm

def inclusion (K : CochainComplex C ℕ) (c : ℕ) :
    (HomologicalComplex.single C (.up ℕ) c).obj (K.homology c) ⟶ truncation K c :=
  (HomologicalComplex.single C (.up ℕ) c).map (cyclesHomologyIso K c).inv ≫
    (HomologicalComplex.extendSingleIso (shift c) ((tail K c).cycles 0) 0 c
      (by simp [shift])).inv ≫
    HomologicalComplex.extendMap (zeroCyclesMap (tail K c)) (shift c)

variable (K : CochainComplex C ℕ) (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

include hK in
theorem projection_quasiIso : QuasiIso (projection K c) := by
  apply (K.quasiIso_πTruncGE_iff_isSupported (shift c)).mpr
  constructor
  intro q hq
  apply hK q
  rintro rfl
  exact hq 0 (by simp [shift])

include hK in
theorem tail_positive_exact (q : ℕ) : (tail K c).ExactAt (q + 1) := by
  have : QuasiIso (projection K c) := projection_quasiIso K c hK
  apply ((tail K c).extend_exactAt_iff (shift c) (j := q + 1) rfl).mp
  exact (exactAt_iff_of_quasiIsoAt (projection K c) ((shift c).f (q + 1))).mp
    (hK _ (by simp only [shift, ComplexShape.embeddingUp'Add_f]; omega))

include hK in
theorem inclusion_quasiIso : QuasiIso (inclusion K c) := by
  have : QuasiIso (zeroCyclesMap (tail K c)) :=
    zeroCyclesMap_quasiIso (tail K c) (tail_positive_exact K c hK)
  dsimp only [inclusion]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
