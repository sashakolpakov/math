import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra

/-! # Evaluation Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EvaluationSymmetry.Construction

noncomputable section

/-!
# CartierDuality: symmetry of scalar-extended Cartier evaluation
-/

open _root_.Module TensorProduct Coalgebra

universe u v w

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]
variable (B : Type w) [CommRing B] [Algebra R B]

/-- A pure tensor in the scalar-extended dual acts by the corresponding
scalar multiple of the original dual functional after base change. -/
theorem dualBaseChange_tmul_eval (s : B) (f : DualAlgebra.Construction.DualCoordinate R M) (z : B ⊗[R] M) :
    DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R M B (s ⊗ₜ[R] f) z =
      s * f.ofConv.baseChange B z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [hz, hz', mul_add]
  | tmul t x =>
    simp [DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv_apply, Algebra.smul_def, mul_assoc, mul_comm]

/-- Evaluation of the scalar-extended perfect module pairing is
unchanged when the two factors are exchanged and the original module
is identified with its bidual by evaluation. -/
theorem dualBaseChange_pairing_symmetry (z : B ⊗[R] M) (w : B ⊗[R] DualAlgebra.Construction.DualCoordinate R M) :
    DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R M B w z =
      DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R (DualAlgebra.Construction.DualCoordinate R M) B
        ((DualAlgebra.Construction.dualCoordinateBidualLinearEquiv R M).toLinearMap.baseChange B z) w := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [hz, hz']
  | tmul s x =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp [hw, hw']
    | tmul t f => simp [DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv_apply, mul_comm]

variable (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

local instance e56EvaluationSymmetryDualRing : CommRing (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convCommRing
local instance e56EvaluationSymmetryDualAlgebra : Algebra R (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convAlgebra

/-- Extending the algebra point corresponding to a character and
evaluating a tensor is precisely contraction with that character. -/
theorem characterPoint_tensor_evaluation (z : GroupLike B (B ⊗[R] A))
    (w : B ⊗[R] DualAlgebra.Construction.DualCoordinate R A) :
    ((DualAlgebra.Construction.affineDualPointsEquivCharacters R B A).symm z).toLinearMap.liftBaseChange B w =
      DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A B w z.val := by
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp [hw, hw']
  | tmul s f =>
    rw [LinearMap.liftBaseChange_tmul, dualBaseChange_tmul_eval]
    exact congrArg (fun a : B => s * a)
      (DualAlgebra.Construction.affineDualPointsEquivCharacters_symm_apply_dual R B A z f)

/-- The same contraction identity, expressed using an arbitrary point
of the dual coordinate algebra. -/
theorem algebraPoint_tensor_evaluation (q : DualAlgebra.Construction.DualCoordinate R A →ₐ[R] B)
    (w : B ⊗[R] DualAlgebra.Construction.DualCoordinate R A) :
    q.toLinearMap.liftBaseChange B w =
      DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A B w
        (DualAlgebra.Construction.affineDualPointsEquivCharacters R B A q).val := by
  have h := characterPoint_tensor_evaluation R B A (DualAlgebra.Construction.affineDualPointsEquivCharacters R B A q) w
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- The algebra point induced by bidual evaluation. -/
def bidualEvaluationAlgPoint (p : A →ₐ[R] B) :
    DualAlgebra.Construction.DualCoordinate R (DualAlgebra.Construction.DualCoordinate R A) →ₐ[R] B :=
  p.comp (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A).symm.toAlgEquiv.toAlgHom

/-- The induced double-dual point evaluates an original evaluation
functional by the original algebra point. -/
theorem bidualEvaluationAlgPoint_eval (p : A →ₐ[R] B) (a : A) :
    bidualEvaluationAlgPoint R B A p (DualAlgebra.Construction.dualCoordinateBidualLinearEquiv R A a) = p a := by
  change p ((DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A).symm
    ((DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A) a)) = p a
  rw [BialgEquiv.symm_apply_apply]

/-- Scalar extension of the double-dual point, composed with evaluation,
is scalar extension of the original point. -/
theorem bidualEvaluationAlgPoint_tensor (p : A →ₐ[R] B) (z : B ⊗[R] A) :
    (bidualEvaluationAlgPoint R B A p).toLinearMap.liftBaseChange B
        ((DualAlgebra.Construction.dualCoordinateBidualLinearEquiv R A).toLinearMap.baseChange B z) =
      p.toLinearMap.liftBaseChange B z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [hz, hz']
  | tmul s a =>
    simp only [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
    exact congrArg (fun b : B => s • b) (bidualEvaluationAlgPoint_eval R B A p a)

/-- The two affine character evaluations agree after swapping the
original point and the dual point, using the actual bidual evaluation map. -/
theorem affineCharacterEvaluation_symmetry (p : A →ₐ[R] B) (q : DualAlgebra.Construction.DualCoordinate R A →ₐ[R] B) :
    q.toLinearMap.liftBaseChange B
        (DualAlgebra.Construction.affineDualPointsEquivCharacters R B (DualAlgebra.Construction.DualCoordinate R A)
          (bidualEvaluationAlgPoint R B A p)).val =
      p.toLinearMap.liftBaseChange B (DualAlgebra.Construction.affineDualPointsEquivCharacters R B A q).val := by
  let z := (DualAlgebra.Construction.affineDualPointsEquivCharacters R B A q).val
  let w := (DualAlgebra.Construction.affineDualPointsEquivCharacters R B (DualAlgebra.Construction.DualCoordinate R A)
    (bidualEvaluationAlgPoint R B A p)).val
  have hq := algebraPoint_tensor_evaluation R B A q w
  have hp := algebraPoint_tensor_evaluation R B (DualAlgebra.Construction.DualCoordinate R A)
    (bidualEvaluationAlgPoint R B A p)
      ((DualAlgebra.Construction.dualCoordinateBidualLinearEquiv R A).toLinearMap.baseChange B z)
  exact hq.trans ((dualBaseChange_pairing_symmetry R A B z w).trans
    (hp.symm.trans (bidualEvaluationAlgPoint_tensor R B A p z)))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EvaluationSymmetry.Construction
