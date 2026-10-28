import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Smooth -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.Smooth

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A product over an algebraically closed field is preirreducible when its
factors are irreducible, of finite type on the left, and smooth on the right. -/
theorem tensor_preirreducible {K : Type u} [Field K] [IsAlgClosed K]
    (X Y : Over (Spec (.of K))) [IrreducibleSpace X.left] [IrreducibleSpace Y.left]
    [LocallyOfFiniteType X.hom] [Smooth Y.hom] :
    IsPreirreducible (Set.univ : Set (X ⊗ Y).left) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : Smooth (fst X Y).left := by dsimp; infer_instance
  let e : (𝟙_ (Over (Spec (.of K))) ⊗ Y).left ≅ Y.left :=
    (Over.forget _).mapIso (λ_ Y)
  have : IrreducibleSpace (𝟙_ (Over (Spec (.of K))) ⊗ Y).left :=
    e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
  have hfiber (x : X.left) (hx : x ∈ closedPoints X.left) :
      IsPreirreducible ((fst X Y).left ⁻¹' {x}) := by
    let p : 𝟙_ (Over (Spec (.of K))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (by simp)
    let α : 𝟙_ (Over (Spec (.of K))) ⊗ Y ⟶ X ⊗ Y := p ⊗ₘ 𝟙 Y
    have hrange : Set.range α.left = (fst X Y).left ⁻¹' {x} := by
      dsimp [α]
      rw [Over.tensorHom_left]
      simp [Scheme.Pullback.range_map, p]
      congr 1
      ext z
      simp [pointOfClosedPoint_apply, eq_comm]
    simpa only [Set.image_univ, hrange] using
      ((IrreducibleSpace.isIrreducible_univ _).image α.left
        α.left.continuous.continuousOn).isPreirreducible
  have hdense : (Set.univ : Set X.left) ⊆
      closure (Set.univ ∩ {x | IsPreirreducible ((fst X Y).left ⁻¹' {x})}) := by
    calc
      Set.univ = closure (closedPoints X.left) := closure_closedPoints.symm
      _ ⊆ closure (Set.univ ∩ {x | IsPreirreducible ((fst X Y).left ⁻¹' {x})}) :=
        closure_mono (fun x hx => ⟨Set.mem_univ x, hfiber x hx⟩)
  simpa only [Set.preimage_univ] using
    (PreirreducibleSpace.isPreirreducible_univ (X := X.left)).preimage_of_dense_isPreirreducible_fiber
      (fst X Y).left (fst X Y).left.isOpenMap hdense

/-- Products of smooth integral schemes over an algebraically closed field
are integral. -/
theorem smooth_tensor_integral {K : Type u} [Field K] [IsAlgClosed K]
    (X Y : Over (Spec (.of K))) [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom] : IsIntegral (X ⊗ Y).left := by
  have : Surjective Y.hom :=
    ⟨Function.surjective_to_subsingleton (α := Y.left) (β := Spec _) _⟩
  have : Surjective (fst X Y).left := by dsimp; infer_instance
  have : Nonempty (X ⊗ Y).left :=
    ⟨((fst X Y).left.surjective (Classical.choice inferInstance)).choose⟩
  have : PreirreducibleSpace (X ⊗ Y).left := ⟨tensor_preirreducible X Y⟩
  have : IrreducibleSpace (X ⊗ Y).left := ⟨inferInstance⟩
  have : Smooth (X ⊗ Y).hom := by dsimp; infer_instance
  have : IsReduced (X ⊗ Y).left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (X ⊗ Y).hom
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The product of a complex abelian variety with itself is an integral scheme. -/
theorem abelian_tensor_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IsIntegral (A.toOver ⊗ A.toOver).left := by
  have : IsIntegral A.toOver.left := inferInstanceAs (IsIntegral A.carrier)
  have : Smooth A.toOver.hom := A.variety.presentation.smooth
  exact smooth_tensor_integral A.toOver A.toOver

/-- Connectedness and smoothness supply the integrality required by the
project's variety bundle, without an additional hypothesis on Construction. -/
theorem connected_presentation_integral (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] : IsIntegral X.carrier := by
  let x : X.carrier := Classical.choice inferInstance
  let C : irreducibleComponents X.carrier :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hC : IsClopen (C : Set X.carrier) :=
    ⟨isClosed_of_mem_irreducibleComponents _ C.property, (X.componentOpen C).isOpen⟩
  have hfull : (C : Set X.carrier) = Set.univ :=
    hC.eq_univ ⟨x, mem_irreducibleComponent⟩
  have : IrreducibleSpace X.carrier :=
    (irreducibleSpace_def X.carrier).mpr (by
      change IsIrreducible Set.univ
      rw [← hfull]
      exact C.property.1)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.Albanese.Construction.Smooth
