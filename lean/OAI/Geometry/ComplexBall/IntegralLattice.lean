import OAI.Geometry.ComplexBall.ArithmeticQuotientSplitUnitary
import OAI.NumberTheory.ArithmeticGroups.Lattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

/-! # Integral Lattice -/

namespace OAI.Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient

noncomputable section

section

/-! The full integral lattice O_E^3 in the six-dimensional F=E⁺ coordinates. -/

open scoped Classical _root_.NumberField
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def cmCoordinates (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    ArithmeticQuotientEquationsData.Vec E ≃ₗ[ArithmeticQuotientEquationsData.RealField E] (Fin 6 → ArithmeticQuotientEquationsData.RealField E) :=
  (LinearEquiv.piCongrRight (fun _ : Fin 3 =>
    (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm.toLinearEquiv)).trans
      (ArithmeticQuotientEquationsData.quadraticCoordinates (ArithmeticQuotientEquationsData.imaginarySquare δ hδ))

def integralVectorModule : Submodule (𝓞 (ArithmeticQuotientEquationsData.RealField E)) (ArithmeticQuotientEquationsData.Vec E) where
  carrier := NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.standardLattice (E := E)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' := by
    intro a x hx
    apply (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mpr
    intro i
    change IsIntegral ℤ (algebraMap (𝓞 (ArithmeticQuotientEquationsData.RealField E)) E a * x i)
    apply IsIntegral.mul _ ((NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mp hx i)
    exact map_isIntegral_int (algebraMap (ArithmeticQuotientEquationsData.RealField E) E) a.property

omit [IsCMField E] in
lemma integralVectorModule_finite : (integralVectorModule (E := E)).FG := by
  apply Submodule.FG.of_restrictScalars ℤ
  exact (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.standardLattice_full_stable (E := E)).1

omit [IsCMField E] in
lemma integralVectorModule_full :
    Submodule.span (ArithmeticQuotientEquationsData.RealField E) (integralVectorModule (E := E) : Set (ArithmeticQuotientEquationsData.Vec E)) = ⊤ := by
  have hs := (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.standardLattice_full_stable (E := E)).2.1
  have he : Submodule.span ℚ (integralVectorModule (E := E) : Set (ArithmeticQuotientEquationsData.Vec E)) = ⊤ := hs
  have hle : Submodule.span ℚ (integralVectorModule (E := E) : Set (ArithmeticQuotientEquationsData.Vec E)) ≤
      (Submodule.span (ArithmeticQuotientEquationsData.RealField E) (integralVectorModule (E := E) : Set (ArithmeticQuotientEquationsData.Vec E))).restrictScalars ℚ :=
    Submodule.span_le.mpr (fun _ hx => Submodule.subset_span hx)
  rw [he] at hle
  exact top_unique hle

def cmIntegralLatticeModule (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    Submodule (𝓞 (ArithmeticQuotientEquationsData.RealField E)) (Fin 6 → ArithmeticQuotientEquationsData.RealField E) :=
  (integralVectorModule (E := E)).map
    ((cmCoordinates δ hδ hδ0).toLinearMap.restrictScalars (𝓞 (ArithmeticQuotientEquationsData.RealField E)))

lemma cmIntegralLatticeModule_full (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    Submodule.span (ArithmeticQuotientEquationsData.RealField E) (cmIntegralLatticeModule δ hδ hδ0 : Set (Fin 6 → ArithmeticQuotientEquationsData.RealField E)) = ⊤ := by
  change Submodule.span (ArithmeticQuotientEquationsData.RealField E)
    ((cmCoordinates δ hδ hδ0) '' (integralVectorModule (E := E) : Set (ArithmeticQuotientEquationsData.Vec E))) = ⊤
  change Submodule.span (ArithmeticQuotientEquationsData.RealField E)
    ((cmCoordinates δ hδ hδ0).toLinearMap '' (integralVectorModule (E := E) : Set (ArithmeticQuotientEquationsData.Vec E))) = ⊤
  rw [← Submodule.map_span, integralVectorModule_full, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (cmCoordinates δ hδ hδ0).surjective

def cmIntegralLattice (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice (ArithmeticQuotientEquationsData.RealField E) 6 where
  module := cmIntegralLatticeModule δ hδ hδ0
  finite := (integralVectorModule_finite (E := E)).map _
  full := cmIntegralLatticeModule_full δ hδ hδ0

end

/-! Compatibility of the original E-linear matrix action with the concrete
six-dimensional rational representation and integral lattice. -/

open scoped Classical
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma rationalQuadraticUnitaryEquiv_entry (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd (QuadraticAlgebra (ArithmeticQuotientEquationsData.RealField E) (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) 0))
      (algebraMap (ArithmeticQuotientEquationsData.RealField E) _ (ArithmeticQuotientSplitUnitary.realCoefficient b hb))) (i j : Fin 3) :
    (ArithmeticQuotientSplitUnitary.rationalQuadraticUnitaryEquiv b hb δ hδ hδ0 g).val i j =
      ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 (g.val i j) := rfl

lemma rationalQuadraticUnitaryEquiv_symm_matrix (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (g : ArithmeticQuotientEquationsData.RationalSU b) :
    ((ArithmeticQuotientSplitUnitary.rationalQuadraticUnitaryEquiv b hb δ hδ hδ0).symm g).val.val =
      g.val.val.map (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm := by
  apply Matrix.ext
  intro i j
  let e := ArithmeticQuotientSplitUnitary.rationalQuadraticUnitaryEquiv b hb δ hδ hδ0
  have h := rationalQuadraticUnitaryEquiv_entry b hb δ hδ hδ0 (e.symm g) i j
  change (e (e.symm g)).val i j = _ at h
  rw [e.apply_symm_apply] at h
  apply (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).injective
  change _ = ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 ((ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (g.val i j))
  rw [AlgEquiv.apply_symm_apply]
  exact h.symm

lemma originalUnitaryRationalEquiv_matrix (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (g : ArithmeticQuotientEquationsData.RationalSU b) :
    (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g).val.val =
      ArithmeticQuotientEquationsData.regularMatrix (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) (g.val.val.map (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm) := by
  change ArithmeticQuotientEquationsData.regularMatrix (ArithmeticQuotientEquationsData.imaginarySquare δ hδ)
    ((ArithmeticQuotientSplitUnitary.rationalQuadraticUnitaryEquiv b hb δ hδ hδ0).symm g).val.val = _
  rw [rationalQuadraticUnitaryEquiv_symm_matrix]

lemma cmCoordinates_mulVec (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (A : ArithmeticQuotientEquationsData.Mat E) (x : ArithmeticQuotientEquationsData.Vec E) :
    cmCoordinates δ hδ hδ0 (A.mulVec x) =
      (ArithmeticQuotientEquationsData.regularMatrix (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) (A.map (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm)).mulVec
        (cmCoordinates δ hδ hδ0 x) := by
  have he : (fun i => (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (A.mulVec x i)) =
      (A.map (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm).mulVec
        (fun i => (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (x i)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  change ArithmeticQuotientEquationsData.quadraticCoordinates (ArithmeticQuotientEquationsData.imaginarySquare δ hδ)
    (fun i => (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (A.mulVec x i)) = _
  rw [he, ArithmeticQuotientEquationsData.quadraticCoordinates_mulVec]
  rfl

lemma cmCoordinates_action (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (g : ArithmeticQuotientEquationsData.RationalSU b) (x : ArithmeticQuotientEquationsData.Vec E) :
    cmCoordinates δ hδ hδ0 (Matrix.SpecialLinearGroup.toLin' g.val x) =
      Matrix.SpecialLinearGroup.toLin' (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g).val
        (cmCoordinates δ hδ hδ0 x) := by
  change cmCoordinates δ hδ hδ0 (g.val.val.mulVec x) =
    (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g).val.val.mulVec (cmCoordinates δ hδ hδ0 x)
  rw [originalUnitaryRationalEquiv_matrix]
  exact cmCoordinates_mulVec δ hδ hδ0 g.val.val x

end

end OAI.Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient
