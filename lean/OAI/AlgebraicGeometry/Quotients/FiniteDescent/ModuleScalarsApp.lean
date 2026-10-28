import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Module Scalars App -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars

noncomputable section

/-! Global regular functions acting on actual module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

universe u

variable {X : Scheme.{u}}

def scalar (M : X.Modules) (r : Γ(X, ⊤)) : End M where
  val.app U := ModuleCat.ofHom
    ((X.presheaf.map U.unop.leTop.op r) • (LinearMap.id : Γ(M, U.unop) →ₗ[Γ(X, U.unop)] Γ(M, U.unop)))
  val.naturality {U V} h := by
    ext s
    change Γ(M, U.unop) at s
    change X.presheaf.map V.unop.leTop.op r •
        (show Γ(M, V.unop) from M.presheaf.map h s) =
      M.presheaf.map h (X.presheaf.map U.unop.leTop.op r • s)
    have hr : X.presheaf.map V.unop.leTop.op r =
        X.presheaf.map h (X.presheaf.map U.unop.leTop.op r) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    exact (congrArg (fun a : Γ(X, V.unop) =>
      a • (show Γ(M, V.unop) from M.presheaf.map h s)) hr).trans
        (M.map_smul h.unop (X.presheaf.map U.unop.leTop.op r) s).symm

theorem scalar_app (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (s : Γ(M, U)) :
    (scalar M r).app U s = X.presheaf.map U.leTop.op r • s := rfl

theorem scalar_naturality {M N : X.Modules} (a : M ⟶ N) (r : Γ(X, ⊤)) :
    scalar M r ≫ a = a ≫ scalar N r := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact a.app_smul (X.presheaf.map U.leTop.op r) s

def scalarHom (M : X.Modules) : Γ(X, ⊤) →+* End M where
  toFun := scalar M
  map_one' := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    change X.presheaf.map U.leTop.op (1 : Γ(X, ⊤)) • s = s
    rw [map_one, one_smul]
  map_zero' := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    change X.presheaf.map U.leTop.op (0 : Γ(X, ⊤)) • s = 0
    rw [map_zero, zero_smul]
  map_add' r t := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    change X.presheaf.map U.leTop.op (r + t) • s =
      X.presheaf.map U.leTop.op r • s + X.presheaf.map U.leTop.op t • s
    rw [map_add, add_smul]
  map_mul' r t := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    change X.presheaf.map U.leTop.op (r * t) • s =
      X.presheaf.map U.leTop.op r • (X.presheaf.map U.leTop.op t • s)
    rw [map_mul, mul_smul]

theorem structure_value (r : Γ(X, ⊤)) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (scalar (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) r) = r := by
  change X.presheaf.map (𝟙 (.op ⊤)) r * (1 : Γ(X, ⊤)) = r
  rw [X.presheaf.map_id]
  exact mul_one r

theorem pushforward_scalar {Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pushforward f).map (scalar M (f.appTop r)) =
      scalar ((Scheme.Modules.pushforward f).obj M) r := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change Γ(M, f ⁻¹ᵁ U) at s
  change X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop r) • s =
    f.app U (Y.presheaf.map U.leTop.op r) • s
  exact congrArg (fun a : Γ(X, f ⁻¹ᵁ U) => a • s)
    (ConcreteCategory.congr_hom (f.naturality U.leTop.op) r).symm

/-- Pullback of multiplication by a global function is multiplication by
its pulled-back function on every module sheaf. -/
theorem pullback_scalar {Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (scalar M r) =
      scalar ((Scheme.Modules.pullback f).obj M) (f.appTop r) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_scalar]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality (scalar M r)).symm.trans
    (scalar_naturality ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) r)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleScalarsApp.Construction.ModuleScalars
