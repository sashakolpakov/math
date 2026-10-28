import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.TopBoundary
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel

/-! # Oriented Top Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology

noncomputable section

/-! The top cohomology of the actual dual exterior Koszul complex is the
original quotient, normalized by evaluation on the ordered basis wedge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.TopBoundary
  AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction

universe u
variable (R : Type u) [CommRing R]

abbrev koszul {n : ℕ} (s : Fin n → R) :=
  Exterior.KoszulComplex.complex R (Fin n → R) (GeneratorMatrix.equation R s)

abbrev dualComplex {n : ℕ} (s : Fin n → R) :=
  DualComplexHomology.complex R (koszul R s)

abbrev ideal {n : ℕ} (s : Fin n → R) := Ideal.span (Set.range s)

def evaluation {n : ℕ} (s : Fin n → R) : (dualComplex R s).X n ≃ₗ[R] R :=
  TopBoundary.topDualEquiv R (Pi.basisFun R (Fin n))

theorem outgoing_isZero {n : ℕ} (s : Fin n → R) :
    IsZero ((dualComplex R s).X ((ComplexShape.up ℕ).next n)) := by
  have hz := Exterior.PowerVanishing.subsingleton (Pi.basisFun R (Fin n)) (Nat.lt_succ_self n)
  let : Subsingleton ((dualComplex R s).X ((ComplexShape.up ℕ).next n)) := by
    rw [CochainComplex.next]
    change Subsingleton (Module.Dual R (⋀[R]^(n + 1) (Fin n → R)))
    let := hz
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

theorem dual_d {m n : ℕ} (s : Fin m → R) :
    ((dualComplex R s).d n (n + 1)).hom =
      (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (GeneratorMatrix.equation R s) n).dualMap := by
  dsimp only [dualComplex, DualComplexHomology.complex, Functor.mapHomologicalComplex_obj_d,
    HomologicalComplex.op_d, ExactModuleDualFunctor.functor]
  rw [Exterior.KoszulHomotopy.complex_d]
  rfl

theorem incoming_range {n : ℕ} (s : Fin n → R) :
    (((dualComplex R s).d ((ComplexShape.up ℕ).prev n) n).hom.range).map
      (evaluation R s).toLinearMap = ideal R s := by
  cases n with
  | zero =>
      have hd : (dualComplex R s).d ((ComplexShape.up ℕ).prev 0) 0 = 0 := by
        apply (dualComplex R s).shape
        simp
      rw [hd]
      simp [ideal, Set.range_eq_empty]
  | succ n =>
      rw [show (ComplexShape.up ℕ).prev (n + 1) = n from CochainComplex.prev_nat_succ n]
      rw [← LinearMap.range_comp, dual_d]
      change (TopBoundary.boundaryValue R s).range = ideal R s
      exact TopBoundary.boundary_range R s

def quotientEquiv {n : ℕ} (s : Fin n → R) :
    ((dualComplex R s).X n ⧸
      ((dualComplex R s).d ((ComplexShape.up ℕ).prev n) n).hom.range) ≃ₗ[R] (R ⧸ ideal R s) :=
  Submodule.Quotient.equiv _ _ (evaluation R s) (incoming_range R s)

def iso {n : ℕ} (s : Fin n → R) :
    (dualComplex R s).homology n ≅ ModuleCat.of R (R ⧸ ideal R s) :=
  TopHomologyCokernel.quotientIso (dualComplex R s) n (outgoing_isZero R s) ≪≫
    (quotientEquiv R s).toModuleIso

theorem cycleClass_iso {n : ℕ} (s : Fin n → R) :
    TopHomologyCokernel.cycleClass (dualComplex R s) n (outgoing_isZero R s) ≫
      (iso R s).hom = ModuleCat.ofHom
        ((ideal R s).mkQ.comp (evaluation R s).toLinearMap) := by
  rw [iso, Iso.trans_hom, ← Category.assoc, TopHomologyCokernel.cycleClass_quotientIso]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology
