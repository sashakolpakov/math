import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPresheaf

/-! # Bilinear Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Natural bilinear maps of sheaves give bilinear maps on sections over any chosen coefficient ring. In particular, the actual tensor sheaf has its canonical coefficient-bilinear section pairing. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

section
variable {M N P Q : X.Modules} (β : Bilinear.Sheaves.SheafBilinearMap M N P)

def Bilinear.Sheaves.SheafBilinearMap.coefficientApp (c : R →+* Γ(X, ⊤)) (U : X.Opens) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op U) →ₗ[R]
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op U) →ₗ[R]
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c P).obj (op U) where
  toFun x :=
    { toFun := β.app U x
      map_add' := (β.app U x).map_add
      map_smul' r y := (β.app U x).map_smul (Coefficient.AlgebraPresheaf.coefficientSectionMap c U r) y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact LinearMap.congr_fun ((β.app U).map_add x y) z
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    exact LinearMap.congr_fun ((β.app U).map_smul (Coefficient.AlgebraPresheaf.coefficientSectionMap c U r) x) y

theorem Bilinear.Sheaves.SheafBilinearMap.coefficientApp_naturality (c : R →+* Γ(X, ⊤))
    {U V : X.Opens} (h : V ⟶ U)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op U))
    (y : (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op U)) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c P).map h.op (β.coefficientApp c U x y) =
      β.coefficientApp c V ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map h.op x)
        ((Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map h.op y) :=
  β.naturality h x y

theorem Bilinear.Sheaves.SheafBilinearMap.coefficientApp_postcomp (c : R →+* Γ(X, ⊤)) (f : P ⟶ Q)
    (U : X.Opens) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op U))
    (y : (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op U)) :
    (β.postcomp f).coefficientApp c U x y =
      ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map f).app (op U) (β.coefficientApp c U x y) := rfl

end

def Coefficient.BilinearSections.coefficientTensorSectionPairing (c : R →+* Γ(X, ⊤)) (M N : X.Modules) (U : X.Opens) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op U) →ₗ[R]
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op U) →ₗ[R]
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c (Tensor.ProductSheaf.tensorModule M N)).obj (op U) :=
  (Tensor.Bifunctor.tensorBilinear M N).coefficientApp c U

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
