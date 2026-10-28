/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechCochains.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic

/-! # Cochains -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

open _root_.AddCommGrpCat
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace

/-!
# Concrete Cech cochains on topological spaces

This file gives an elementwise description of mathlib's Cech complex for presheaves of
abelian groups and connects its intersection opens to affine quasicoherent vanishing.
The construction follows mathlib PR #35073, specialized to the API needed here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe v u

namespace AddCommGrpCat

/-- The categorical product of additive commutative groups is isomorphic to the
corresponding dependent function group. -/
noncomputable def productIsoPi {ι : Type u} (X : ι → AddCommGrpCat.{u}) :
    ∏ᶜ X ≅ .of (∀ i, X i) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (HasLimit.productLimitCone X).isLimit

/-- The forward product isomorphism is componentwise projection. -/
@[simp]
theorem productIsoPi_hom_apply {ι : Type u} (X : ι → AddCommGrpCat.{u})
    (x : (∏ᶜ X :)) (i : ι) : (productIsoPi X).hom x i = Pi.π X i x :=
  ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _)
      (HasLimit.productLimitCone X).isLimit ⟨i⟩) x

/-- Every component of the inverse product isomorphism is evaluation. -/
@[simp]
theorem productIsoPi_inv_apply {ι : Type u} (X : ι → AddCommGrpCat.{u})
    (x : ∀ i, X i) (i : ι) : Pi.π X i ((productIsoPi X).inv x) = x i :=
  ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _)
      (HasLimit.productLimitCone X).isLimit ⟨i⟩) x

end AddCommGrpCat

namespace TopologicalSpace

variable {T : Type u} [TopologicalSpace T]
variable (F : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {ι : Type u}
variable (U : ι → Opens T) (n : ℕ)

/-- Degree `n` of the Cech complex consists of families of sections indexed by
`(n + 1)`-tuples of cover indices. -/
noncomputable def cechCochainAddEquiv :
    ((cechComplexFunctor U).obj F).X n ≃+
      ∀ i : Fin (n + 1) → ι,
        F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  (Cochains.AddCommGrpCat.productIsoPi fun i : Fin (n + 1) → ι =>
    F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))).addCommGroupIsoToAddEquiv

@[simp]
theorem cechCochainAddEquiv_apply
    (x : ((cechComplexFunctor U).obj F).X n) (i : Fin (n + 1) → ι) :
    cechCochainAddEquiv F U n x i =
      Pi.π (fun i : Fin (n + 1) → ι =>
        F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) i x :=
  Cochains.AddCommGrpCat.productIsoPi_hom_apply _ _ _

@[simp]
theorem cechCochainAddEquiv_symm_apply_component
    (x : ∀ i : Fin (n + 1) → ι,
      F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k))))
    (i : Fin (n + 1) → ι) :
    Pi.π (fun i : Fin (n + 1) → ι =>
      F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) i
        ((cechCochainAddEquiv F U n).symm x) = x i :=
  Cochains.AddCommGrpCat.productIsoPi_inv_apply _ _ _

private noncomputable def Opens.piObjIsoIInf
    {κ : Type v} (V : κ → Opens T) :
    ∏ᶜ V ≅ ⨅ k, V k :=
  IsLimit.conePointUniqueUpToIso
    (limit.isLimit _) (Preorder.isLimitIInf V)

theorem Opens.piObj_eq_iInf {κ : Type v} (V : κ → Opens T) :
    (∏ᶜ V) = ⨅ k, V k :=
  (Cochains.TopologicalSpace.Opens.piObjIsoIInf V).to_eq

end TopologicalSpace

/-- In a separated scheme, the product open attached to a Cech tuple of
affine opens is affine. -/
theorem IsAffineOpen.cechIntersection
    {X : Scheme.{u}} [X.IsSeparated] {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (i : Fin (n + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)) := by
  rw [show (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)) =
      ⨅ k : Fin (n + 1), U (i k) from
    Cochains.TopologicalSpace.Opens.piObj_eq_iInf _]
  exact IsAffineOpen.iInf (fun k ↦ hU (i k))

end OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains
