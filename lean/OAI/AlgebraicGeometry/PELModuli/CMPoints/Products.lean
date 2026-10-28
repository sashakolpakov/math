import OAI.AlgebraicGeometry.PELModuli.CMPoints.Transport
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Products -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Products

noncomputable section

/-! Finite products of rational weight-one Hodge structures, with
their actual complexification and coefficient conjugation. This is the
linear construction needed for the three rank-one CM factors. -/

open scoped Classical TensorProduct

variable {I U : Type*} [Fintype I] [AddCommGroup U] [Module ℚ U]
  (H : I → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)

def hodgePiCoordinates : ComplexMultiplication.WeightOne.CM.Complexification (I → U) ≃ₗ[ℂ] (I → ComplexMultiplication.WeightOne.CM.Complexification U) :=
  TensorProduct.piRight ℚ ℂ ℂ (fun _ : I => U)

theorem hodgePiCoordinates_conjugate (x : ComplexMultiplication.WeightOne.CM.Complexification (I → U)) (i : I) :
    hodgePiCoordinates (ComplexMultiplication.WeightOne.CM.coefficientConjugation (I → U) x) i =
      ComplexMultiplication.WeightOne.CM.coefficientConjugation U (hodgePiCoordinates x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul z u => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

def hodgePiSubspace (F : I → Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification U)) :
    Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (I → U)) where
  carrier := {x | ∀ i, hodgePiCoordinates x i ∈ F i}
  zero_mem' i := by simp
  add_mem' hx hy i := by
    simpa only [map_add, Pi.add_apply] using (F i).add_mem (hx i) (hy i)
  smul_mem' a x hx i := by
    simpa only [map_smul, Pi.smul_apply] using (F i).smul_mem a (hx i)

theorem hodgePi_complementary :
    IsCompl (hodgePiSubspace (fun i => (H i).holomorphic))
      (hodgePiSubspace (fun i => (H i).antiholomorphic)) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hy
    apply hodgePiCoordinates.injective
    funext i
    exact (Submodule.disjoint_def.mp (H i).complementary.disjoint _ (hx i) (hy i)).trans
      (congrFun (map_zero hodgePiCoordinates) i).symm
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    have hex (i : I) : ∃ u ∈ (H i).holomorphic, ∃ v ∈ (H i).antiholomorphic,
        u + v = hodgePiCoordinates x i := by
      apply Submodule.mem_sup.mp
      rw [(H i).complementary.codisjoint.eq_top]
      trivial
    choose u hu v hv huv using hex
    refine Submodule.mem_sup.mpr ⟨hodgePiCoordinates.symm u, ?_,
      hodgePiCoordinates.symm v, ?_, ?_⟩
    · intro i
      simpa only [LinearEquiv.apply_symm_apply] using hu i
    · intro i
      simpa only [LinearEquiv.apply_symm_apply] using hv i
    · apply hodgePiCoordinates.injective
      rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact funext huv

def hodgePi : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (I → U) := by
  let : Module.Finite ℚ (I → U) := by
    by_cases hI : Nonempty I
    · let i : I := hI.some
      let : FiniteDimensional ℚ U := (H i).finiteDimensional
      infer_instance
    · let : IsEmpty I := not_nonempty_iff.mp hI
      infer_instance
  exact {
    holomorphic := hodgePiSubspace (fun i => (H i).holomorphic)
    antiholomorphic := hodgePiSubspace (fun i => (H i).antiholomorphic)
    complementary := hodgePi_complementary H
    conjugate_mem := fun x => by
      change (∀ i, hodgePiCoordinates (ComplexMultiplication.WeightOne.CM.coefficientConjugation (I → U) x) i ∈
        (H i).antiholomorphic) ↔ ∀ i, hodgePiCoordinates x i ∈ (H i).holomorphic
      simp only [hodgePiCoordinates_conjugate, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.conjugate_mem] }

theorem hodgePiCoordinates_single (i j : I) (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    hodgePiCoordinates ((LinearMap.single ℚ (fun _ : I => U) i).baseChange ℂ x) j =
      if j = i then x else 0 := by
  by_cases hij : j = i
  · subst j
    induction x using TensorProduct.inductionOn with
    | tmul z u => simp [hodgePiCoordinates, LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, ite_true]
  · induction x using TensorProduct.inductionOn with
    | tmul z u => simp [hodgePiCoordinates, LinearMap.baseChange_tmul, hij]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, ite_eq_right hij, add_zero]

theorem hodgePi_single_isHodgeMap (i : I) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (H i) (hodgePi H) (LinearMap.single ℚ (fun _ : I => U) i) := by
  intro x hx j
  rw [hodgePiCoordinates_single]
  split_ifs with hij
  · simpa only [hij] using hx
  · exact (H j).holomorphic.zero_mem

theorem coordinateSubspaces_internal :
    DirectSum.IsInternal (fun i : I => (LinearMap.single ℚ (fun _ : I => U) i).range) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply iSupIndep_def.mpr
    intro i
    have h : Disjoint ({i} : Set I) {j | j ≠ i} := by simp
    simpa using LinearMap.disjoint_single_single ℚ (fun _ : I => U) {i} {j | j ≠ i} h
  · exact LinearMap.iSup_range_single ℚ (fun _ : I => U)

variable (E : Type) [Field E] [Algebra ℚ E] [Module E U] [IsScalarTower ℚ E U]
  {r : ℕ} (H' : Fin r → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
  (hCM : ∀ i, ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H' i))

def cmPiComponent (i : Fin r) : ComplexMultiplication.Decomposition.CM.CMComponent (hodgePi H') := by
  letI : DecidableEq (Fin r) := Classical.decEq _
  let f := LinearMap.single ℚ (fun _ : Fin r => U) i
  have hf : Function.Injective f := by
    intro x y h
    have h' := congrFun h i
    simpa only [f, LinearMap.coe_single, Pi.single_eq_same] using h'
  let e : U ≃ₗ[ℚ] f.range := LinearEquiv.ofInjective f hf
  letI := e.symm.toAddEquiv.module E
  letI := e.symm.isScalarTower (A := E)
  have hlin : f.comp e.symm.toLinearMap = f.range.subtype := by
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  have hh := (hodgePi_single_isHodgeMap H' i).comp ((H' i).transport_symm_isHodgeMap e)
  change ComplexMultiplication.WeightOne.CM.IsHodgeMap ((H' i).transport e) (hodgePi H') (f.comp e.symm.toLinearMap) at hh
  rw [hlin] at hh
  exact {
    subspace := f.range
    hodge := (H' i).transport e
    inclusion_hodge := hh
    field := E
    cm := Realization.rankOneCMAction_transport E (hCM i) e }

/-- The actual coordinate summands make a finite product of rank-one
CM Hodge structures into an internal CM decomposition. -/
def cmPiDecomposition : ComplexMultiplication.Decomposition.CM.CMDecomposition (hodgePi H') where
  numberOfComponents := r
  component := cmPiComponent E H' hCM
  isInternal := by
    let family := fun i : Fin r => (cmPiComponent E H' hCM i).subspace
    have h : letI : DecidableEq (Fin r) := Classical.decEq _
        DirectSum.IsInternal family := coordinateSubspaces_internal (I := Fin r) (U := U)
    have he := congrArg (fun d : DecidableEq (Fin r) =>
      letI := d
      DirectSum.IsInternal family)
      (Subsingleton.elim (Classical.decEq (Fin r)) (inferInstance : DecidableEq (Fin r)))
    exact he.mp h

include hCM in
theorem realization_hasCMH1_of_product (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (hodgePi H')) :
    R.abelianVariety.HasCMH1 :=
  ⟨R.h1HodgeStructure, R.h1HodgeStructure_holomorphic, R.h1HodgeStructure_antiholomorphic,
    ⟨Transport.cmDecompositionTransport (cmPiDecomposition E H' hCM) R.comparison⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Products
