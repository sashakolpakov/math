/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechCochains.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.GroupProductCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FormalCoproductEvaluationAdditive
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Topology.Sheaves.Abelian

/-! # Cochains -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u v w

variable {T : Type u} [TopologicalSpace T]
variable (F : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {ι : Type u}
variable (U : ι → Opens T) (n : ℕ)

/-- Degree `n` of the Cech complex consists of families of sections indexed by
`(n + 1)`-tuples of cover indices. -/
noncomputable def cechCochainAddEquiv :
    ((cechComplexFunctor U).obj F).X n ≃+
      ∀ i : Fin (n + 1) → ι,
        F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  (Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi fun i : Fin (n + 1) → ι =>
    F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))).addCommGroupIsoToAddEquiv

@[simp]
theorem cechCochainAddEquiv_apply
    (x : ((cechComplexFunctor U).obj F).X n) (i : Fin (n + 1) → ι) :
    cechCochainAddEquiv F U n x i =
      Pi.π (fun i : Fin (n + 1) → ι =>
        F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) i x :=
  Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi_hom_apply _ _ _

@[simp]
theorem cechCochainAddEquiv_symm_apply_component
    (x : ∀ i : Fin (n + 1) → ι,
      F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k))))
    (i : Fin (n + 1) → ι) :
    Pi.π (fun i : Fin (n + 1) → ι =>
      F.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) i
        ((cechCochainAddEquiv F U n).symm x) = x i :=
  Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi_inv_apply _ _ _

noncomputable def opensProductIsoIInf
    {κ : Type v} (V : κ → Opens T) :
    ∏ᶜ V ≅ ⨅ k, V k :=
  IsLimit.conePointUniqueUpToIso
    (limit.isLimit _) (Preorder.isLimitIInf V)

theorem topologicalOpensProduct_eq_iInf {κ : Type v} (V : κ → Opens T) :
    (∏ᶜ V) = ⨅ k, V k :=
  (opensProductIsoIInf V).to_eq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cochains
