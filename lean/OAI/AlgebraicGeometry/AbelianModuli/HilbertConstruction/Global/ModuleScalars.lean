import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Module Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars

noncomputable section

/-! Every global regular function acts as an endomorphism of every module sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def globalModuleScalar (M : X.Modules) (r : Γ(X, ⊤)) : End M where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r •
          (LinearMap.id : Γ(M, U.unop) →ₗ[Γ(X, U.unop)] Γ(M, U.unop)))
      naturality := by
        rintro ⟨U⟩ ⟨V⟩ h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        change Γ(M, U) at m
        change X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r •
            (M.presheaf.map h m : Γ(M, V)) =
          M.presheaf.map h (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • m)
        have hM : M.presheaf.map h
            (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • m) =
            X.presheaf.map h (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) •
              (M.presheaf.map h m : Γ(M, V)) := M.map_smul h.unop _ m
        exact (congrArg (fun a : Γ(X, V) => a • (M.presheaf.map h m : Γ(M, V)))
          (ConcreteCategory.congr_hom
            (X.presheaf.map_comp (homOfLE (show U ≤ ⊤ from le_top)).op h) r)).trans hM.symm }

theorem globalModuleScalar_app (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (m : Γ(M, U)) :
    (globalModuleScalar M r).app U m =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • m := rfl

theorem globalModuleScalar_natural {M N : X.Modules} (r : Γ(X, ⊤)) (φ : M ⟶ N) :
    globalModuleScalar M r ≫ φ = φ ≫ globalModuleScalar N r := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro m
  exact φ.app_smul _ m

theorem globalModuleScalar_structure_value (r : Γ(X, ⊤)) :
    Frame.Coordinates.structureModuleEndValue X (globalModuleScalar (Line.Bundles.structureModule X) r) = r := by
  change X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) r * 1 = r
  rw [X.presheaf.map_id]
  exact mul_one r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars
