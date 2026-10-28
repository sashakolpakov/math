import OAI.RepresentationTheory.Theta.Adelic.UnitaryPolynomialEquations
import OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

/-! # Unitary Algebraic Model -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel

/-! The actual arbitrary-form special-unitary group as an affine matrix
group, with an explicit identification of its rational points. -/

open scoped Classical

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.PrincipalSubgroup
open OAI.RepresentationTheory.Theta.Adelic.UnitaryPolynomialEquations

def unitaryPolynomial {R : Type*} [CommRing R] (d : R)
    (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d)) (e : Geometry.ComplexBall.ArithmeticQuotientEquationsData.EquationIndex) : Geometry.ComplexBall.ArithmeticQuotientEquationsData.GroundPolynomial R :=
  UnitaryPolynomialEquations.matrixEquation (MvPolynomial.C d) (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d MvPolynomial.C)) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.variableMatrix R) e

theorem unitaryPolynomial_eval {R S : Type*} [CommRing R] [CommRing S]
    (d : R) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic R d))
    (f : R →+* S) (M : Matrix (Fin 6) (Fin 6) S) (e : Geometry.ComplexBall.ArithmeticQuotientEquationsData.EquationIndex) :
    MvPolynomial.eval₂Hom f (fun ij => M ij.1 ij.2) (unitaryPolynomial d H e) =
      UnitaryPolynomialEquations.matrixEquation (f d) (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f)) M e := by
  let φ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.GroundPolynomial R →+* S := MvPolynomial.eval₂Hom f (fun ij => M ij.1 ij.2)
  have hM : (Geometry.ComplexBall.ArithmeticQuotientEquationsData.variableMatrix R).map φ = M := by
    ext i j
    simp [Geometry.ComplexBall.ArithmeticQuotientEquationsData.variableMatrix, φ]
  change φ (UnitaryPolynomialEquations.matrixEquation (MvPolynomial.C d)
    (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d MvPolynomial.C)) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.variableMatrix R) e) = _
  rw [UnitaryPolynomialEquations.matrixEquation_map, hM]
  have hH : (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d MvPolynomial.C)).map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap (MvPolynomial.C d) φ) =
      H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d (φ.comp MvPolynomial.C)) := by
    rfl
  have hφ : φ.comp MvPolynomial.C = f := by
    ext x
    simp [φ]
  rw [hH]
  change UnitaryPolynomialEquations.matrixEquation ((φ.comp MvPolynomial.C) d)
    (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d (φ.comp MvPolynomial.C))) M e = _
  rw [hφ]

variable {F : Type} [Field F] (d : F) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))

def unitaryAlgebraicGroup : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F 6 where
  equations := Set.range (unitaryPolynomial d H)
  subgroup K _ f := UnitaryPolynomialEquations.unitaryImage (f d) (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f))
  mem_iff K _ f M := by
    change M ∈ UnitaryPolynomialEquations.unitaryImage (f d) (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f)) ↔
      ∀ p ∈ Set.range (unitaryPolynomial d H),
        MvPolynomial.eval₂Hom f (fun ij => M.val ij.1 ij.2) p = 0
    constructor
    · intro h p hp
      obtain ⟨e, rfl⟩ := hp
      rw [unitaryPolynomial_eval]
      exact (UnitaryPolynomialEquations.matrixEquation_zero_iff (f d) (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f)) M).mpr h e
    · intro h
      apply (UnitaryPolynomialEquations.matrixEquation_zero_iff (f d) (H.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f)) M).mp
      intro e
      rw [← unitaryPolynomial_eval d H f M.val e]
      exact h _ ⟨e, rfl⟩

def regularUnitaryPoints : SpecialUnitary.SU H →* (unitaryAlgebraicGroup d H).RationalPoints where
  toFun g := ⟨UnitaryPolynomialEquations.regularSU d H g, ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one (UnitaryPolynomialEquations.regularSU d H))
  map_mul' g h := Subtype.ext (map_mul (UnitaryPolynomialEquations.regularSU d H) g h)

theorem regularUnitaryPoints_bijective : Function.Bijective (regularUnitaryPoints d H) := by
  constructor
  · intro g h he
    have hh := Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularSpecialLinear_injective d (congrArg Subtype.val he)
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val hh
  · intro g
    obtain ⟨h, hh⟩ := g.property
    exact ⟨h, Subtype.ext hh⟩

def regularUnitaryEquiv : SpecialUnitary.SU H ≃* (unitaryAlgebraicGroup d H).RationalPoints :=
  MulEquiv.ofBijective (regularUnitaryPoints d H) (regularUnitaryPoints_bijective d H)

end RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel

namespace RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel.Topology

/-! The polynomial unitary realization has exactly the native topology
on matrix units, with continuous coordinate extraction in both directions. -/

open scoped Classical
open _root_.Topology

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel

attribute [local fun_prop] Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
variable (d : F) (H : Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))

omit [T2Space F] in
theorem regularMatrix_continuous : Continuous (Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  obtain ⟨⟨i, a⟩, rfl⟩ := Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex.surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := Geometry.ComplexBall.ArithmeticQuotientEquationsData.pairIndex.surjective j
  simp_rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix_entry]
  fin_cases a <;> fin_cases b <;> dsimp [Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticRegular] <;> fun_prop

omit [IsTopologicalRing F] [T2Space F] in
theorem decodeMatrix_continuous : Continuous (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply (Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff d _).mpr
  constructor <;> dsimp [Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix] <;> fun_prop

omit [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] in
theorem regularUnitaryEquiv_inverse_matrix
    (g : (unitaryAlgebraicGroup d H).RationalPoints) :
    ((regularUnitaryEquiv d H).symm g).val.val = Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d g.val.val := by
  let e := regularUnitaryEquiv d H
  have he := congrArg (fun q : (unitaryAlgebraicGroup d H).RationalPoints =>
    q.val.val) (e.apply_symm_apply g)
  change Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix d (e.symm g).val.val = g.val.val at he
  exact (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decode_regularMatrix d (e.symm g).val.val).symm.trans (congrArg (Geometry.ComplexBall.ArithmeticQuotientEquationsData.decodeMatrix d) he)

omit [T2Space F] in
theorem regularUnitaryEquiv_continuous :
    Continuous (regularUnitaryEquiv d H) := by
  have h := (regularMatrix_continuous d).comp
    (Units.continuous_val.comp (continuous_subtype_val : Continuous (fun g : SpecialUnitary.SU H => g.val)))
  exact (h.subtype_mk _).subtype_mk _

omit [T2Space F] in
theorem regularUnitaryEquiv_inverse_continuous :
    Continuous (regularUnitaryEquiv d H).symm := by
  let e := regularUnitaryEquiv d H
  have hv : Continuous (fun g : (unitaryAlgebraicGroup d H).RationalPoints =>
      (e.symm g).val.val) :=
    ((decodeMatrix_continuous d).comp (continuous_subtype_val.comp continuous_subtype_val)).congr
      (fun g => (regularUnitaryEquiv_inverse_matrix d H g).symm)
  apply continuous_induced_rng.mpr
  change Continuous (fun g => (e.symm g).val)
  apply Units.continuous_iff.mpr
  refine ⟨hv, ?_⟩
  apply (hv.comp continuous_inv).congr
  intro g
  change (e.symm g⁻¹).val.val = ((e.symm g).val⁻¹).val
  rw [map_inv]
  rfl

def regularUnitaryContinuousEquiv : SpecialUnitary.SU H ≃ₜ*
    (unitaryAlgebraicGroup d H).RationalPoints where
  toMulEquiv := regularUnitaryEquiv d H
  continuous_toFun := regularUnitaryEquiv_continuous d H
  continuous_invFun := regularUnitaryEquiv_inverse_continuous d H

end RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel.Topology

end

end OAI
