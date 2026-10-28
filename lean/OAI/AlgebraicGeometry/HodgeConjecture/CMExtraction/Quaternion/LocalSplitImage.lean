import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalHermitianMatrix
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.SplitImage

/-! # Local Split Image -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalSplitImage

noncomputable section

/-! The binary image calculation for an arbitrary specified local
completion equivalence and its literal matrix projection. -/

open scoped Classical _root_.NumberField _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra

variable (F : Type) [Field F] [NumberField F] (a b : F)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (hH : H.val = UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b))
  (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) [CharZero (v.adicCompletion F)]
  (r : v.adicCompletion F) (hr : r ^ 2 = RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) a) (hr0 : r ≠ 0)
  {K : Type} [Field K] (e : v.adicCompletion F ≃+* K)
  (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) →* Matrix.SpecialLinearGroup (Fin 3) K)

theorem quaternionLocalHermitian_split_image
    (hp : ∀ g, (p g).val = (g.val.val.map (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0)).map e)
    (hb : b ≠ 0) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v),
      p (HermitianAdeles.quaternionLocalHermitian F a b H hH v g) = QuadraticUnitary.activeBinaryBlock A := by
  let A₀ := Matrix.SpecialLinearGroup.map e.symm.toRingHom A
  obtain ⟨g, hg⟩ := SplitImage.quaternionPointUnitary_split_image a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v))
    r hr hr0 hb A₀
  have hA : (QuadraticUnitary.activeBinaryMatrix A₀.val).map e = (QuadraticUnitary.activeBinaryBlock A).val := by
    change (QuadraticUnitary.activeBinaryMatrix A₀.val).map e = QuadraticUnitary.activeBinaryMatrix A.val
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [QuadraticUnitary.activeBinaryMatrix, A₀]
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact (hp _).trans ((congrArg
    (fun M : Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F a (.inr v)) => (M.map (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0)).map e)
    (LocalHermitianMatrix.quaternionLocalHermitian_matrix F a b H hH v g)).trans
    ((congrArg (fun M : Matrix (Fin 3) (Fin 3) (v.adicCompletion F) => M.map e) hg).trans hA))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalSplitImage
