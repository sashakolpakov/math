import OAI.NumberTheory.Quaternion.Arithmetic.SplitPolynomialHom

/-! # Split Adeles -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SplitAdeles

noncomputable section

/-! Unconditional strong approximation for quaternion norm-one
matrix groups that split over the number field. -/

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem splitQuaternion_curve_generation (a b x y : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) (v : LocalAdeles.Place F) :
    Subgroup.closure (PolynomialCurveTransport.groundFieldCurveElements (MatrixGroup.quaternionNormOneMatrixGroup a b) v) = ⊤ :=
  (SplitPolynomialHom.splitQuaternionPolynomialHom a b x y ha hb h).groundField_curve_generation v
    (SplitPolynomialHom.splitQuaternionPolynomialHom_surjective a b x y ha hb h (LocalAdeles.localEmbedding v))
    (SpecialLinearAdeles.specialLinear_curve_generation v)

theorem strongApproximation_splitQuaternion (a b x y : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) (S : Finset (LocalAdeles.Place F))
    (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) :
    DenseRange (LocalAdeles.diagonalAway (MatrixGroup.quaternionNormOneMatrixGroup a b) S) :=
  PolynomialCurveTransport.strongApproximation_of_groundField_curve_generation _ S harch
    (fun v => splitQuaternion_curve_generation a b x y ha hb h v.val)

end

end OAI.NumberTheory.Quaternion.Arithmetic.SplitAdeles
