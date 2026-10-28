import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluationField
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ParameterPoints

/-! # Intrinsic Evaluation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts

noncomputable section

/-! Simultaneous evaluation of native finite etale schemes over a single
constructed finite field extension, retaining each family's own labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

theorem native_joint_finite_evaluation_field (K : Type u) [Field K]
    {I : Type u} [Fintype I] (X : I → Over (Spec (.of K)))
    [∀ i, IsFinite (X i).hom] [∀ i, Etale (X i).hom] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (n : I → ℕ), ∀ i, Nonempty (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) (ULift.{u} (Fin (n i))) ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj (X i)) := by
  have ha (i : I) : ∃ C : (CommAlgCat K)ᵒᵖ, Nonempty ((algSpec (.of K)).obj C ≅ X i) :=
    (essImage_algSpec (R := .of K) (G := X i)).mpr (isAffine_of_isAffineHom (X i).hom)
  choose C he using ha
  let e i := Classical.choice (he i)
  have hfinite (i : I) : Module.Finite K (C i).unop := Intrinsic.ComponentLift.Components.finite_coordinates_of_iso K (e i)
  have hetale (i : I) : Algebra.Etale K (C i).unop := Intrinsic.ComponentLift.Components.etale_coordinates_of_iso K (e i)
  obtain ⟨L, _, _, _, hsplit⟩ := EvaluationField.Lifts.exists_joint_finite_evaluation_field K (fun i ↦ (C i).unop)
  have hs (i : I) : ∃ n : ℕ, Nonempty ((L ⊗[K] (C i).unop) ≃ₐ[L] (Fin n → L)) :=
    (hsplit i).nonempty_algEquiv_fun
  choose n hn using hs
  refine ⟨L, inferInstance, inferInstance, inferInstance, n, ?_⟩
  intro i
  let a := (Classical.choice (hn i)).trans
    (AlgEquiv.piCongrLeft' L (fun _ : Fin (n i) ↦ L) Equiv.ulift.symm)
  exact ⟨Intrinsic.EvaluationField.Lifts.constantAffineIso L (n i) ≪≫ Intrinsic.EvaluationField.Lifts.affineAlgebraIso L a ≪≫
    (AffineSpecialFiber.Components.affineBaseChangeIso K L (C i).unop).symm ≪≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso (e i)⟩

structure JointFiniteEvaluationField (K : Type u) [Field K]
    {I : Type u} (X : I → Over (Spec (.of K))) where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finite : Module.Finite K carrier]
  count : I → ℕ
  parameterIso : ∀ i, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of carrier)) (ULift.{u} (Fin (count i))) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K carrier)))).obj (X i)

attribute [instance] JointFiniteEvaluationField.field JointFiniteEvaluationField.algebra
  JointFiniteEvaluationField.finite

def jointFiniteEvaluationField (K : Type u) [Field K]
    {I : Type u} [Fintype I] (X : I → Over (Spec (.of K)))
    [∀ i, IsFinite (X i).hom] [∀ i, Etale (X i).hom] : JointFiniteEvaluationField K X :=
  Classical.choice (show Nonempty (JointFiniteEvaluationField K X) from by
    obtain ⟨L, _, _, _, n, h⟩ := native_joint_finite_evaluation_field K X
    exact ⟨{carrier := L, count := n, parameterIso i := Classical.choice (h i)}⟩)

def JointFiniteEvaluationField.family {K : Type u} [Field K]
    {I : Type u} {X : I → Over (Spec (.of K))} (d : JointFiniteEvaluationField K X)
    (i : I) : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField K (X i) where
  carrier := d.carrier
  count := d.count i
  parameterIso := d.parameterIso i

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts
