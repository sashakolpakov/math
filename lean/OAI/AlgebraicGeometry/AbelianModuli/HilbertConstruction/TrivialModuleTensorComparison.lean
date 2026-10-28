import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureModuleTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSheafNaturality

/-! # Trivial Module Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialModuleTensorComparison

noncomputable section

/-! A chosen module trivialization transports affine-open invertibility of the tensor comparison from the structure module. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u v

private theorem isIso_of_isoSquare {C : Type u} [Category.{v} C] {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B') [IsIso g] (a : A ≅ A') (b : B ≅ B')
    (h : a.hom ≫ g = f ≫ b.hom) : IsIso f := by
  have hf : f = a.hom ≫ g ≫ b.inv := by
    apply (cancel_mono b.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm
  rw [hf]
  infer_instance

theorem affineOpen_trivialModuleTensorComparison_isIso
    {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules) (e : M ≅ Line.Bundles.structureModule X)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op U)) := by
  let F := Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f.appTop.hom
  let T := (AlgebraSectionModules.commAlgToModules Γ(S, ⊤)).obj (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
  let c := (F.mapIso e).app (.op U)
  let d := (F.mapIso ((Scheme.Modules.pushforward a).mapIso ((Scheme.Modules.pullback a).mapIso e))).app (.op U)
  let α := (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op U)
  let β := (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H (Line.Bundles.structureModule X)).app (.op U)
  have h : (T ◁ c.hom) ≫ β = α ≫ d.hom :=
    NatTrans.congr_app (Module.TensorSheafNaturality.moduleSectionTensorComparison_sheaf_natural (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      a f.appTop.hom b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) e.hom) (.op U)
  have : IsIso β := Affine.StructureModuleTensorComparison.affineOpen_structureModuleTensorComparison_isIso H U hU
  exact isIso_of_isoSquare α β ((tensorLeft T).mapIso c) d h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialModuleTensorComparison
