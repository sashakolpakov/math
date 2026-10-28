import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap

/-! # Scalar Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarNaturality.FormsBaseChange

noncomputable section

/-! The canonical affine scalar map is natural for actual algebra maps in a commutative base-change square. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal
open scoped TensorProduct

universe u

variable (R S A B A' B' : Type u)
  [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]
  [Algebra R A'] [Algebra R B'] [Algebra A' B'] [Algebra S B']
  [IsScalarTower R A' B'] [IsScalarTower R S B']
  (f : CommAlgCat.of R A ⟶ CommAlgCat.of R A')
  (g : CommAlgCat.of S B ⟶ CommAlgCat.of S B')
  (h : ∀ a, algebraMap A' B' (f a) = g (algebraMap A B a))

include h in
theorem formExtensionMap_naturality (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    ScalarMap.FormsBaseChange.formExtensionMap R S A' B' n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap g n (ScalarMap.FormsBaseChange.formExtensionMap R S A B n ω) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v a =>
    change ScalarMap.FormsBaseChange.formExtensionMap R S A' B' n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap g n (ScalarMap.FormsBaseChange.formExtensionMap R S A B n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
    exact (congrArg (ScalarMap.FormsBaseChange.formExtensionMap R S A' B' n) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol f n a v)).trans
      ((ScalarMap.FormsBaseChange.formExtensionMap_symbol R S A' B' (f a) (fun i => f (v i))).trans
        ((congrArg₂ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B') (h a) (funext (fun i => h (v i)))).trans
          ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol g n (algebraMap A B a) (fun i => algebraMap A B (v i))).symm.trans
            (congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap g n) (ScalarMap.FormsBaseChange.formExtensionMap_symbol R S A B a v)).symm)))

include h in
theorem formScalarMap_naturality (n : ℕ) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    ScalarMap.FormsBaseChange.formScalarMap R S A' B' n ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n).baseChange S x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap g n (ScalarMap.FormsBaseChange.formScalarMap R S A B n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s ω =>
    rw [LinearMap.baseChange_tmul, ScalarMap.FormsBaseChange.formScalarMap_tmul, ScalarMap.FormsBaseChange.formScalarMap_tmul, map_smul,
      formExtensionMap_naturality R S A B A' B' f g h]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarNaturality.FormsBaseChange
