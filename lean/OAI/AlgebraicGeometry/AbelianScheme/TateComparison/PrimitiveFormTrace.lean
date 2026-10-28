import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceAllTests

/-! # Primitive Form Trace -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Primitive actual one-forms take algebraic branch sums to sums of
pullbacks on every affine test, including nonreduced tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {A : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj A] [IsCommMonObj A]

def PrimitiveFormTrace.IsPrimitiveOneForm (ω : FormConstants.OneForms A) : Prop :=
  ∀ (R : CommAlgCat.{0} ℂ) (x y : FormConstants.affineComplexTest R ⟶ A), ω.val R (x * y) = ω.val R x + ω.val R y

def PrimitiveFormTrace.primitiveFormPointHom (ω : FormConstants.OneForms A) (hω : PrimitiveFormTrace.IsPrimitiveOneForm ω) (R : CommAlgCat.{0} ℂ) :
    Additive (FormConstants.affineComplexTest R ⟶ A) →+ KaehlerDifferential ℂ R where
  toFun x := ω.val R x.toMul
  map_zero' := by
    have h := hω R 1 1
    rw [one_mul] at h
    exact (add_eq_left.mp h.symm)
  map_add' x y := hω R x.toMul y.toMul

theorem PrimitiveFormTrace.primitiveForm_prod (ω : FormConstants.OneForms A) (hω : PrimitiveFormTrace.IsPrimitiveOneForm ω) (R : CommAlgCat.{0} ℂ)
    {I : Type*} (s : Finset I) (x : I → (FormConstants.affineComplexTest R ⟶ A)) :
    ω.val R (∏ i ∈ s, x i) = ∑ i ∈ s, ω.val R (x i) := by
  have h := map_sum (PrimitiveFormTrace.primitiveFormPointHom ω hω R) (fun i => Additive.ofMul (x i)) s
  exact h

theorem PrimitiveFormTrace.primitiveForm_div (ω : FormConstants.OneForms A) (hω : PrimitiveFormTrace.IsPrimitiveOneForm ω) (R : CommAlgCat.{0} ℂ)
    (x y : FormConstants.affineComplexTest R ⟶ A) : ω.val R (x / y) = ω.val R x - ω.val R y :=
  (PrimitiveFormTrace.primitiveFormPointHom ω hω R).map_sub (Additive.ofMul x) (Additive.ofMul y)

theorem PrimitiveFormTrace.primitiveForm_constant_translate (ω : FormConstants.OneForms A) (hω : PrimitiveFormTrace.IsPrimitiveOneForm ω)
    (p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A) (R : CommAlgCat.{0} ℂ)
    (x : FormConstants.affineComplexTest R ⟶ A) (a : FormConstants.affineComplexTest R ⟶ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) :
    ω.val R (x / (a ≫ p)) = ω.val R x := by
  rw [PrimitiveFormTrace.primitiveForm_div ω hω, FormConstants.forms_at_constant, sub_zero]

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (C : Correspondences.EtaleCorrespondence X)
  [IsReduced X.left] [IsLocallyNoetherian X.left] [IsSeparated A.hom]

theorem Correspondences.EtaleCorrespondence.algebraicTrace_primitiveForm (a : X ⟶ A) (ω : FormConstants.OneForms A) (hω : PrimitiveFormTrace.IsPrimitiveOneForm ω) :
    Branches.IsBranchTrace C (FormConstants.formsPullback a ω) (FormConstants.formsPullback (C.algebraicTrace a) ω) := by
  intro R x n e
  change ω.val R (x ≫ C.algebraicTrace a) =
    ∑ i : Fin n, ω.val R (C.endpoint (C.splitBranch x e i) ≫ a)
  rw [C.algebraicTrace_local a x e]
  exact PrimitiveFormTrace.primitiveForm_prod ω hω R Finset.univ _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
