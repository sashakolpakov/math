import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices
import OAI.RepresentationTheory.Theta.Adelic.SubringCongruence

/-! # Integral Model Congruence -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralModelCongruence

noncomputable section

/-! Actual integral lifts and finite-index reduction kernels for the
standard lattice stabilizer of a polynomial matrix group. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction OAI.RepresentationTheory.Theta.Adelic.SubringCongruence

theorem specialLinear_map_injective {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := I) f) := by
  intro g h he
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply hf
  exact congrArg (fun A : Matrix.SpecialLinearGroup I S => A.val i j) he

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)

abbrev IntegralGroup := G.latticeStabilizer (NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n)

def integralMatrix (g : IntegralGroup G) : Matrix.SpecialLinearGroup (Fin n) (𝓞 F) :=
  ((NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction.standard_lattice_stabilizer_iff_integral G g.val).mp g.property).choose

theorem integralMatrix_map (g : IntegralGroup G) :
    Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) F) (integralMatrix G g) = g.val.val :=
  ((NumberTheory.ArithmeticGroups.Lattices.Integral.Matrices.Construction.standard_lattice_stabilizer_iff_integral G g.val).mp g.property).choose_spec

def integralMatrixHom : IntegralGroup G →* Matrix.SpecialLinearGroup (Fin n) (𝓞 F) where
  toFun := integralMatrix G
  map_one' := by
    apply specialLinear_map_injective (algebraMap (𝓞 F) F) NumberField.RingOfIntegers.coe_injective
    rw [integralMatrix_map, map_one]
    rfl
  map_mul' g h := by
    apply specialLinear_map_injective (algebraMap (𝓞 F) F) NumberField.RingOfIntegers.coe_injective
    rw [integralMatrix_map, map_mul, integralMatrix_map, integralMatrix_map]
    rfl

def integerIdeal (N : ℕ) : Ideal (𝓞 F) := Ideal.span {(N : 𝓞 F)}

def integralReduction (N : ℕ) : IntegralGroup G →*
    Matrix.SpecialLinearGroup (Fin n) (𝓞 F ⧸ integerIdeal (F := F) N) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk _)).comp (integralMatrixHom G)

theorem integralReduction_finiteIndex (N : ℕ) (hN : 0 < N) :
    (integralReduction G N).ker.FiniteIndex := by
  have hn : (N : 𝓞 F) ≠ 0 := by exact_mod_cast hN.ne'
  have hI : integerIdeal (F := F) N ≠ ⊥ := by
    intro h
    have hm : (N : 𝓞 F) ∈ integerIdeal (F := F) N := Ideal.subset_span (Set.mem_singleton _)
    rw [h] at hm
    exact hn hm
  let : Finite (𝓞 F ⧸ integerIdeal (F := F) N) := Ring.HasFiniteQuotients.finiteQuotient hI
  infer_instance

theorem integralReduction_coefficients (N : ℕ) (g : IntegralGroup G)
    (hg : g ∈ (integralReduction G N).ker) (i j : Fin n) :
    ∃ x : 𝓞 F, g.val.val.val i j - (1 : Matrix (Fin n) (Fin n) F) i j = (N : F) * (x : F) := by
  let q := Ideal.Quotient.mk (integerIdeal (F := F) N)
  have he := congrArg (fun A : Matrix.SpecialLinearGroup (Fin n) (𝓞 F ⧸ integerIdeal (F := F) N) =>
    A.val i j) hg
  change q ((integralMatrix G g).val i j) = (1 : Matrix (Fin n) (Fin n) (𝓞 F ⧸ integerIdeal (F := F) N)) i j at he
  have he' : q ((integralMatrix G g).val i j) = q ((1 : Matrix (Fin n) (Fin n) (𝓞 F)) i j) :=
    he.trans (SubringCongruence.map_one_entry q i j).symm
  have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he'
  change (integralMatrix G g).val i j - (1 : Matrix (Fin n) (Fin n) (𝓞 F)) i j ∈
    Ideal.span {(N : 𝓞 F)} at hm
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hm
  have h := congrArg (algebraMap (𝓞 F) F) hx
  have hc := congrArg (fun A : Matrix.SpecialLinearGroup (Fin n) F => A.val i j) (integralMatrix_map G g)
  change algebraMap (𝓞 F) F ((integralMatrix G g).val i j) = g.val.val.val i j at hc
  rw [map_sub, map_mul, map_natCast, SubringCongruence.map_one_entry] at h
  exact ⟨x, (congrArg (fun a : F => a - (1 : Matrix (Fin n) (Fin n) F) i j) hc.symm).trans h⟩

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralModelCongruence
