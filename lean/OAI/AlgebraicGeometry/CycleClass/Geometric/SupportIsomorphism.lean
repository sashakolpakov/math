import OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports

/-! # Support Isomorphism -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SupportIsomorphism

noncomputable section

/-!
# Transport of algebraic cycle supports under scheme isomorphisms

The maps in this file come from actual scheme isomorphisms. They preserve
codimension and carry the irreducible closed support to its ordinary image.
No cohomology group or cycle class map is introduced here.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y Z : Scheme.{u}}

/-- Scheme isomorphisms preserve the codimension of every scheme point. -/
@[simp] theorem schemeIso_coheight (e : X ≅ Y) (x : X) :
    Order.coheight (e.hom x) = Order.coheight x :=
  AlgebraicGeometry.coheight_eq_of_isOpenImmersion e.hom

/-- The equivalence on codimension-`p` points induced by a scheme isomorphism. -/
def cyclePointIsoEquiv (e : X ≅ Y) (p : ℕ) : Foundations.Scheme.CycleSupports.CyclePoint X p ≃ Foundations.Scheme.CycleSupports.CyclePoint Y p where
  toFun x := ⟨e.hom x.1, (schemeIso_coheight e x.1).trans x.2⟩
  invFun y := ⟨e.inv y.1, (schemeIso_coheight e.symm y.1).trans y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (Scheme.homeoOfIso e).left_inv x.1
  right_inv y := by
    apply Subtype.ext
    exact (Scheme.homeoOfIso e).right_inv y.1

@[simp] theorem cyclePointIsoEquiv_apply_val (e : X ≅ Y) (p : ℕ)
    (x : Foundations.Scheme.CycleSupports.CyclePoint X p) : (cyclePointIsoEquiv e p x).1 = e.hom x.1 := rfl

@[simp] theorem cyclePointIsoEquiv_symm (e : X ≅ Y) (p : ℕ) :
    (cyclePointIsoEquiv e p).symm = cyclePointIsoEquiv e.symm p := rfl

@[simp] theorem cyclePointIsoEquiv_refl (p : ℕ) :
    cyclePointIsoEquiv (Iso.refl X) p = Equiv.refl (Foundations.Scheme.CycleSupports.CyclePoint X p) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem cyclePointIsoEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) (p : ℕ) :
    cyclePointIsoEquiv (e.trans f) p =
      (cyclePointIsoEquiv e p).trans (cyclePointIsoEquiv f p) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- Transport of irreducible codimension-`p` closed supports. -/
def irreducibleCycleSupportIsoEquiv (e : X ≅ Y) (p : ℕ) :
    Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p ≃ Foundations.Scheme.CycleSupports.IrreducibleCycleSupport Y p :=
  (Foundations.Scheme.CycleSupports.irreducibleCycleSupportEquivCyclePoint X p).trans
    ((cyclePointIsoEquiv e p).trans (Foundations.Scheme.CycleSupports.irreducibleCycleSupportEquivCyclePoint Y p).symm)

/-- The transported support is the image under the underlying scheme map. -/
theorem irreducibleCycleSupportIsoEquiv_coe (e : X ≅ Y) (p : ℕ)
    (V : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p) :
    ((irreducibleCycleSupportIsoEquiv e p V).1 : Set Y) = e.hom '' (V.1 : Set X) := by
  let x := Foundations.Scheme.CycleSupports.irreducibleCycleSupportEquivCyclePoint X p V
  have hx : (V.1 : Set X) = closure ({x.1} : Set X) := by
    simpa only [x, Equiv.symm_apply_apply] using Foundations.Scheme.CycleSupports.cyclePoint_support_coe X p x
  change closure ({e.hom x.1} : Set Y) = e.hom '' (V.1 : Set X)
  rw [hx]
  simpa only [Scheme.coe_homeoOfIso, Set.image_singleton] using
    ((Scheme.homeoOfIso e).image_closure ({x.1} : Set X)).symm

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SupportIsomorphism
