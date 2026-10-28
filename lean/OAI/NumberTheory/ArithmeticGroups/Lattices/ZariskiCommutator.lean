import OAI.NumberTheory.ArithmeticGroups.Lattices.Zariski
import OAI.NumberTheory.ArithmeticGroups.Lattices.SeparateClosure

/-! # Zariski Commutator -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ZariskiCommutator.Construction

noncomputable section

/-! Commutator maps in the specified geometric topology and solvable
subgroup closure. -/

open scoped Classical commutatorElement
open Set _root_.MvPolynomial _root_.Topology

variable {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)

local instance commutatorGeometricTopology : TopologicalSpace G.GeometricPoints := G.geometricTopology

theorem geometric_singleton_closed (g : G.GeometricPoints) : IsClosed ({g} : Set G.GeometricPoints) := by
  have he : ({g} : Set G.GeometricPoints) =
      ⋂ i, ⋂ j, {x : G.GeometricPoints |
        Algebraic.evaluateMatrix (RingHom.id _) x.val (X (i, j) - C (g.val i j)) = 0} := by
    ext x
    simp only [mem_singleton_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro rfl i j
      simp [Algebraic.evaluateMatrix]
    · intro h
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      simpa [Algebraic.evaluateMatrix, sub_eq_zero] using h i j
  rw [he]
  exact isClosed_iInter fun i => isClosed_iInter fun j => Zariski.Construction.geometric_polynomial_zero_closed G _

theorem geometric_commutator_left_continuous (g : G.GeometricPoints) :
    Continuous (fun x : G.GeometricPoints => ⁅x, g⁆) := by
  let Mg : Matrix (Fin n) (Fin n) (AlgebraicClosure k) := g.val
  let Mgi : Matrix (Fin n) (Fin n) (AlgebraicClosure k) := (g⁻¹).val
  let Xmat : Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n (AlgebraicClosure k)) :=
    fun i j => X (i, j)
  let Cg : Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n (AlgebraicClosure k)) :=
    MvPolynomial.C.mapMatrix Mg
  let Cgi : Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n (AlgebraicClosure k)) :=
    MvPolynomial.C.mapMatrix Mgi
  let P := Xmat * Cg * Xmat.adjugate * Cgi
  apply Zariski.Construction.geometric_polynomial_map_continuous G _ (fun ij => P ij.1 ij.2)
  intro x i j
  let Mx : Matrix (Fin n) (Fin n) (AlgebraicClosure k) := x.val
  let e := Algebraic.evaluateMatrix (RingHom.id (AlgebraicClosure k)) x.val
  have hX : e.mapMatrix Xmat = Mx := by
    ext a b
    change e (X (a, b)) = x.val a b
    simp [e, Algebraic.evaluateMatrix]
  have hC (M : Matrix (Fin n) (Fin n) (AlgebraicClosure k)) :
      e.mapMatrix (MvPolynomial.C.mapMatrix M) = M := by
    ext a b
    simp [e, Algebraic.evaluateMatrix]
  have hP : e.mapMatrix P = Mx * Mg * Mx.adjugate * Mgi := by
    change e.mapMatrix (Xmat * Cg * Xmat.adjugate * Cgi) = _
    rw [map_mul, map_mul, map_mul, hX, hC, e.map_adjugate, hX, hC]
  have heval := congrArg (fun M : Matrix (Fin n) (Fin n) (AlgebraicClosure k) => M i j) hP
  change (Mx * Mg * Mx.adjugate * Mgi) i j = e (P i j)
  exact heval.symm

theorem geometric_commutator_right_continuous (g : G.GeometricPoints) :
    Continuous (fun x : G.GeometricPoints => ⁅g, x⁆) := by
  have h := (Zariski.Construction.geometric_inv_continuous G).comp (geometric_commutator_left_continuous G g)
  have he : (fun x : G.GeometricPoints => ⁅g, x⁆) = Inv.inv ∘ (fun x => ⁅x, g⁆) := by
    funext x
    simp only [Function.comp_apply, commutatorElement_inv]
  rw [he]
  exact h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ZariskiCommutator.Construction
