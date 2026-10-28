import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.TensorRestriction

/-! # Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor powers of line bundles remain locally free of rank one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {X : Scheme.{u}} {P : X.Modules} {n : ℕ}

/-- Multiplication of local functions is the universal tensor power of the structure module. -/
def LineBundle.Powers.structureModuleTensorMap (X : Scheme.{u}) (n : ℕ) :
    Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n (Line.Bundles.structureModule X) where
  app U := MultilinearMap.mkPiAlgebra Γ(X, U) (Fin n) Γ(X, U)
  naturality {U V} h s := by
    change (Fin n → Γ(X, U)) at s
    change X.presheaf.map h.op (∏ i, s i) = ∏ i, X.presheaf.map h.op (s i)
    exact map_prod (X.presheaf.map h.op).hom _ _

/-- A multilinear map out of copies of the structure sheaf is determined by its value on ones. -/
def Tensor.Powers.SheafMultilinearMap.unitToHom (β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n P) :
    Line.Bundles.structureModule X ⟶ P where
  val.app U := (ModuleCat.ofHom
    ((LinearMap.id : Γ(X, U.unop) →ₗ[Γ(X, U.unop)] Γ(X, U.unop)).smulRight
      (β.app U.unop (fun _ => (1 : Γ(X, U.unop))))) :
      ModuleCat.of Γ(X, U.unop) Γ(X, U.unop) ⟶ ModuleCat.of Γ(X, U.unop) Γ(P, U.unop))
  val.naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X, U.unop) at r
    have hv : P.val.map h (β.app U.unop (fun _ => (1 : Γ(X, U.unop)))) =
        β.app V.unop (fun _ => (1 : Γ(X, V.unop))) :=
      (β.naturality h.unop (fun _ => (1 : Γ(X, U.unop)))).trans
        (congrArg (β.app V.unop) (funext (fun _ => (X.presheaf.map h).hom.map_one)))
    exact (congrArg (fun a : Γ(P, V.unop) => (show Γ(X, V.unop) from X.presheaf.map h r) • a) hv).symm.trans
      (P.val.map_smul h r (β.app U.unop (fun _ => (1 : Γ(X, U.unop))))).symm

theorem LineBundle.Powers.structureModuleTensorMap_postcomp_unitToHom
    (β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n P) :
    (LineBundle.Powers.structureModuleTensorMap X n).postcomp β.unitToHom = β := by
  apply Tensor.Powers.SheafMultilinearMap.ext
  intro U
  apply MultilinearMap.ext_ring
  change (∏ _i : Fin n, (1 : Γ(X, U))) • β.app U (fun _ => (1 : Γ(X, U))) =
    β.app U (fun _ => (1 : Γ(X, U)))
  simp only [Finset.prod_const_one, one_smul]

theorem LineBundle.Powers.unitToHom_structureModuleTensorMap_postcomp (f : Line.Bundles.structureModule X ⟶ P) :
    ((LineBundle.Powers.structureModuleTensorMap X n).postcomp f).unitToHom = f := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, U) at r
  change r • f.app U (show Γ(X, U) from ∏ _i : Fin n, (1 : Γ(X, U))) = f.app U r
  rw [Finset.prod_const_one]
  have hf := (f.app_smul r (1 : Γ(X, U))).symm
  change r • f.app U (1 : Γ(X, U)) = f.app U (r * (1 : Γ(X, U))) at hf
  exact hf.trans (congrArg (fun a : Γ(X, U) => f.app U a) (mul_one r))

/-- Every tensor power of the structure module is the structure module. -/
theorem LineBundle.Powers.structureModule_isTensorPower (X : Scheme.{u}) (n : ℕ) :
    Tensor.Powers.IsTensorPower (Line.Bundles.structureModule X) n (Line.Bundles.structureModule X) := by
  refine ⟨LineBundle.Powers.structureModuleTensorMap X n, fun P => ?_⟩
  exact ⟨fun f g h => (LineBundle.Powers.unitToHom_structureModuleTensorMap_postcomp f).symm.trans
      ((congrArg Tensor.Powers.SheafMultilinearMap.unitToHom h).trans (LineBundle.Powers.unitToHom_structureModuleTensorMap_postcomp g)),
    fun β => ⟨β.unitToHom, LineBundle.Powers.structureModuleTensorMap_postcomp_unitToHom β⟩⟩

/-- The actual tensor power of a line bundle, with local triviality proved from its frames. -/
def Line.Bundles.LineBundle.tensorPower (L : Line.Bundles.LineBundle X) (n : ℕ) : Line.Bundles.LineBundle X where
  sheaf := TensorPower.PowerSheaf.tensorPowerModule L.sheaf n
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
    refine ⟨U, hx, ?_⟩
    exact (((TensorPower.PowerSheaf.tensorPowerModule_isTensorPower L.sheaf n).pullback_of_isOpenImmersion U.ι).of_sourceIso e).unique
      (LineBundle.Powers.structureModule_isTensorPower U.toScheme n)

/-- The constructed line-bundle power satisfies the original tensor-power predicate. -/
theorem Line.Bundles.LineBundle.tensorPower_isTensorPower (L : Line.Bundles.LineBundle X) (n : ℕ) :
    Tensor.Powers.IsTensorPower L.sheaf n (L.tensorPower n).sheaf :=
  TensorPower.PowerSheaf.tensorPowerModule_isTensorPower L.sheaf n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
