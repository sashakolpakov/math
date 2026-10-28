import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafExactness
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Double Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DoubleAnnihilator.Construction

noncomputable section

/-!
# CartierDuality: the double annihilator as an equality of actual subgroup sheaves
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

namespace SelfDuality

/-- Transposing the defining quotient-dual comparison factors the
double-annihilator map through the original quotient. -/
theorem transpose_quotient_factor {C : Type u} [Category.{v} C] (D : Cᵒᵖ ⥤ C)
    (β : ∀ X : C, X ⟶ D.obj (Opposite.op (D.obj (Opposite.op X))))
    (hn : ∀ {X Y : C} (f : X ⟶ Y), β X ≫ D.map (D.map f.op).op = f ≫ β Y)
    {G K A Q : C} (r : K ⟶ D.obj (Opposite.op G)) (a : A ⟶ K)
    (q : G ⟶ Q) (t : A ⟶ D.obj (Opposite.op Q))
    (h : a ≫ r = t ≫ D.map q.op) :
    (β G ≫ D.map r.op) ≫ D.map a.op = q ≫ (β Q ≫ D.map t.op) := by
  calc
    (β G ≫ D.map r.op) ≫ D.map a.op = β G ≫ D.map (a ≫ r).op := by
      rw [op_comp, D.map_comp, Category.assoc]
    _ = β G ≫ D.map (t ≫ D.map q.op).op := by rw [h]
    _ = q ≫ (β Q ≫ D.map t.op) := by
      rw [op_comp, D.map_comp, ← Category.assoc, hn q, Category.assoc]

end SelfDuality

namespace Exactness

/-- A subgroup in an abelian category is the kernel of its quotient,
as an equality of subobjects. -/
theorem kernel_cokernel_subobject {C : Type u} [Category.{v} C] [Abelian C]
    {G : C} (H : Subobject G) : kernelSubobject (cokernel.π H.arrow) = H := by
  let K : ShortComplex C := ShortComplex.mk H.arrow (cokernel.π H.arrow) (cokernel.condition H.arrow)
  have h : K.Exact := K.exact_of_g_is_cokernel (cokernelIsCokernel H.arrow)
  have he := (K.exact_iff_image_eq_kernel).mp h
  exact he.symm.trans ((imageSubobject_mono H.arrow).trans (Subobject.mk_arrow H))

end Exactness

namespace Schemes

/-- If the quotient has canonical Cartier biduality, taking the
annihilator twice under a perfect pairing recovers the original subgroup. -/
theorem sheafAnnihilator_double {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) (H : Subobject G) (he : e.IsPerfect)
    [IsIso (SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (SheafQuotients.Construction.Schemes.sheafQuotient H))] :
    SheafQuotients.Construction.Schemes.sheafAnnihilator e.flip (SheafQuotients.Construction.Schemes.sheafAnnihilator e H) = H := by
  let t := SheafQuotients.Construction.Schemes.annihilatorToQuotientDual e H
  let : IsIso t := SheafQuotients.Construction.Schemes.annihilatorToQuotientDual_isIso e H he
  let d : CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (SheafQuotients.Construction.Schemes.sheafQuotient H)) ⟶
      CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (SheafQuotients.Construction.Schemes.sheafAnnihilator e H : CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map t.op
  let : IsIso d := (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map_isIso t.op
  let q : G ⟶ SheafQuotients.Construction.Schemes.sheafQuotient H := cokernel.π H.arrow
  let p : SheafQuotients.Construction.Schemes.sheafQuotient H ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (SheafQuotients.Construction.Schemes.sheafAnnihilator e H : CommutativeSheavesAb.Construction.Schemes.FppfAb S) :=
    SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (SheafQuotients.Construction.Schemes.sheafQuotient H) ≫ d
  let : IsIso p := (asIso (SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (SheafQuotients.Construction.Schemes.sheafQuotient H)) ≪≫ asIso d).isIso_hom
  have hf : e.flip.rightAdjoint ≫
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (SheafQuotients.Construction.Schemes.sheafAnnihilator e H).arrow.op =
      cokernel.π H.arrow ≫ (SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (SheafQuotients.Construction.Schemes.sheafQuotient H) ≫ d) :=
    SelfDuality.transpose_quotient_factor (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) SheafEvaluation.Construction.Schemes.sheafBidualEvaluation
      (fun a => SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_natural a) e.rightAdjoint (SheafQuotients.Construction.Schemes.sheafAnnihilator e H).arrow
      (cokernel.π H.arrow) t (SheafQuotients.Construction.Schemes.annihilatorToQuotientDual_fac e H).symm
  change kernelSubobject (e.flip.rightAdjoint ≫
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (SheafQuotients.Construction.Schemes.sheafAnnihilator e H).arrow.op) = H
  have hk : kernelSubobject (cokernel.π H.arrow ≫
      (SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (SheafQuotients.Construction.Schemes.sheafQuotient H) ≫ d)) = kernelSubobject (cokernel.π H.arrow) :=
    kernelSubobject_comp_mono q p
  exact (congrArg (fun a : G ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (SheafQuotients.Construction.Schemes.sheafAnnihilator e H : CommutativeSheavesAb.Construction.Schemes.FppfAb S) =>
    kernelSubobject a) hf).trans (hk.trans
      (@Exactness.kernel_cokernel_subobject (CommutativeSheavesAb.Construction.Schemes.FppfAb S) inferInstance (SheafExactness.Construction.Schemes.fppfAbAbelian S) G H))

end Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DoubleAnnihilator.Construction
