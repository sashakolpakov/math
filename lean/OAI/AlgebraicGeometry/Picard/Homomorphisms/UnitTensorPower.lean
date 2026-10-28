import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

/-! # Unit Tensor Power -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitTensorPower

noncomputable section

/-! The structure module represents each of its tensor powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (X : Scheme.{u}) (n : ℕ)

def unitTensorMultilinear : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) n (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) where
  app U := MultilinearMap.mkPiAlgebra Γ(X, U) (Fin n) Γ(X, U)
  naturality {U V} h s := by
    change X.presheaf.map h.op (∏ i, s i) = ∏ i, X.presheaf.map h.op (s i)
    exact map_prod (X.presheaf.map h.op).hom _ _

def unitMultilinearToHom {P : X.Modules} (β : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) n P) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P where
  val.app U := ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(X, U.unop) Γ(P, U.unop)
    (β.app U.unop (fun _ => (1 : Γ(X, U.unop)))))
  val.naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X, U.unop) at r
    change (show Γ(X, V.unop) from X.presheaf.map h r) •
        β.app V.unop (fun _ => (1 : Γ(X, V.unop))) =
      P.val.map h (r • β.app U.unop (fun _ => (1 : Γ(X, U.unop))))
    erw [P.val.map_smul]
    apply congrArg ((show Γ(X, V.unop) from X.presheaf.map h r) • ·)
    have hn := (β.naturality h.unop (fun _ => (1 : Γ(X, U.unop)))).symm
    change β.app V.unop (fun _ => X.presheaf.map h (1 : Γ(X, U.unop))) = _ at hn
    erw [map_one] at hn
    exact hn

theorem unitTensorMultilinear_postcomp {P : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) n P) :
    (unitTensorMultilinear X n).postcomp (unitMultilinearToHom X n β) = β := by
  apply AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.ext
  intro U
  apply MultilinearMap.ext
  intro s
  change (Fin n → Γ(X, U)) at s
  change (∏ i, s i) • β.app U (fun _ => (1 : Γ(X, U))) = β.app U s
  have h := ((β.app U).map_smul_univ s (fun _ => (1 : Γ(X, U)))).symm
  change (∏ i, s i) • β.app U (fun _ => (1 : Γ(X, U))) = β.app U (fun i => s i * 1) at h
  exact h.trans (congrArg (β.app U) (funext (fun i => mul_one (s i))))

theorem unitMultilinearToHom_postcomp {P : X.Modules} (f : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) :
    unitMultilinearToHom X n ((unitTensorMultilinear X n).postcomp f) = f := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, U) at r
  have hprod : (unitTensorMultilinear X n).app U (fun _ => (1 : Γ(X, U))) =
      (1 : Γ(X, U)) := by
    change (∏ _ : Fin n, (1 : Γ(X, U))) = 1
    exact Finset.prod_const_one
  change r • f.app U ((unitTensorMultilinear X n).app U (fun _ => (1 : Γ(X, U)))) = _
  erw [hprod]
  exact (f.app_smul r (1 : Γ(X, U))).symm.trans
    (congrArg (fun a : Γ(X, U) => f.app U a) (mul_one r))

theorem unit_isTensorPower : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) n (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  refine ⟨unitTensorMultilinear X n, fun P => ⟨?_, ?_⟩⟩
  · intro f g h
    have h' := congrArg (unitMultilinearToHom X n) h
    simpa only [unitMultilinearToHom_postcomp] using h'
  · intro β
    exact ⟨unitMultilinearToHom X n β, unitTensorMultilinear_postcomp X n β⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitTensorPower
