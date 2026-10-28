import OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly

/-! # Base Change -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange.Construction

noncomputable section

/-! Rational coordinates commute with the actual local tensor action.
These identities use only the compatibility of the chosen frames. -/

open scoped Classical Kronecker

variable (F : Type) [Field F] [NumberField F]
  (d : F) (n m : ℕ)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (P : Assembly.Construction.GlobalFrames F d n m H K)

theorem tensorLinear_rational (v : ArchimedeanAdeles.Construction.Places F)
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) (x : TensorSpace.Construction.TensorPosition d n m) :
    TensorSpace.Construction.tensorLinear (Assembly.Construction.localizedUnit F d H v).val (Assembly.Construction.localizedUnit F d K v).val
        (Integral.Construction.rationalPairLocal F H.val K.val v g)
        (fun j => Integral.Construction.rationalQuadraticLocal F d v (x j)) =
      fun j => Integral.Construction.rationalQuadraticLocal F d v (TensorSpace.Construction.tensorLinear H.val K.val g x j) := by
  funext i
  change ((g.1.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) ⊗ₖ
      g.2.val.val.map (Integral.Construction.rationalQuadraticLocal F d v)).mulVec
      (fun j => Integral.Construction.rationalQuadraticLocal F d v (x j))) i =
    Integral.Construction.rationalQuadraticLocal F d v ((g.1.val.val ⊗ₖ g.2.val.val).mulVec x i)
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem frame_symm_rational (v : ArchimedeanAdeles.Construction.Places F) (y : TensorSpace.Construction.StandardPhase (k := F) n m) :
    (P.localFrame v).coordinates.symm (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (y i)) =
      fun j => Integral.Construction.rationalQuadraticLocal F d v (P.rational.coordinates.symm y j) := by
  apply (P.localFrame v).coordinates.injective
  apply funext
  intro i
  rw [LinearEquiv.apply_symm_apply, P.coordinates_compatible]
  simp

theorem coordinateAction_rational (v : ArchimedeanAdeles.Construction.Places F)
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) (y : TensorSpace.Construction.StandardPhase (k := F) n m) :
    TensorSpace.Construction.coordinateAction (Assembly.Construction.localizedUnit F d H v).val (Assembly.Construction.localizedUnit F d K v).val
        (P.localFrame v) (Integral.Construction.rationalPairLocal F H.val K.val v g)
        (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (y i)) =
      fun i => ArchimedeanAdeles.Construction.rationalScalar F v (TensorSpace.Construction.coordinateAction H.val K.val P.rational g y i) := by
  change (P.localFrame v).coordinates
    (TensorSpace.Construction.tensorLinear _ _ _ ((P.localFrame v).coordinates.symm _)) = _
  rw [frame_symm_rational, tensorLinear_rational]
  funext i
  exact P.coordinates_compatible v _ i

theorem localDualAction_rational (v : ArchimedeanAdeles.Construction.Places F)
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :
    Assembly.Construction.localDualAction F d n m H K P v (Integral.Construction.rationalPairLocal F H.val K.val v g) =
      Vacuum.Construction.rationalSymplecticLocal F (n * m) v
        (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g) := by
  apply Subtype.ext
  ext i j
  change TensorSpace.Construction.coordinateAction _ _ (P.localFrame v) _ (Pi.single j 1) i =
    ArchimedeanAdeles.Construction.rationalScalar F v (TensorSpace.Construction.coordinateAction H.val K.val P.rational g (Pi.single j 1) i)
  have he : (Pi.single j 1 : TensorSpace.Construction.StandardPhase (k := ArchimedeanAdeles.Construction.Completion F v) n m) =
      fun a => ArchimedeanAdeles.Construction.rationalScalar F v ((Pi.single j 1 : TensorSpace.Construction.StandardPhase (k := F) n m) a) := by
    funext a
    by_cases h : a = j
    · subst a; simp
    · simp [Pi.single_eq_of_ne h]
  rw [he]
  exact congrFun (coordinateAction_rational F d n m H K P v g (Pi.single j 1)) i

variable (hd : d ≠ 0) (C : Characters.Construction.GlobalCharacters F d n m)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

theorem adelicDualPairAction_rational (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :
    Assembly.Construction.adelicDualPairAction F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) =
      Vacuum.Construction.rationalSymplectic F (n * m) (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g) := by
  apply RestrictedProduct.ext
  intro v
  exact localDualAction_rational F d n m H K P v g

theorem constructedAdelicLift_rational_covers (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :
    Vacuum.Construction.globalProjection F (n * m) C.ψ
        (Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g)) =
      Vacuum.Construction.rationalSymplectic F (n * m) (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g) := by
  rw [Assembly.Construction.constructedAdelicLift_covers, adelicDualPairAction_rational]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange.Construction
