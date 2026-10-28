import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitLeftNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleMonomorphisms

/-! # Section Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplication

noncomputable section

/-! Multiplication by a line-bundle section acts on every module sheaf. In a frame of the line bundle, the actual tensor map becomes multiplication by its actual regular-function coordinate. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

def moduleSectionMultiply (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) : M ⟶ Tensor.ProductSheaf.tensorModule L.sheaf M :=
  (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Tensor.Bifunctor.tensorModuleMap s (𝟙 M)

theorem tensorModuleUnitLeftIso_scalar (M : X.Modules) (a : End (Line.Bundles.structureModule X)) :
    Tensor.Bifunctor.tensorModuleMap a (𝟙 M) ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom =
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom ≫ Global.ModuleScalars.globalModuleScalar M (Frame.Coordinates.structureModuleEndValue X a) := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (Line.Bundles.structureModule X) M M).injective
  rw [← Tensor.Bifunctor.tensorBilinear_postcomp, Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, Tensor.Bifunctor.tensorModuleMap_spec,
    ← Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, Tensor.Bifunctor.tensorBilinear_postcomp,
    Tensor.PullbackUnits.tensorModuleUnitLeftIso_formula, Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
    Tensor.PullbackUnits.tensorModuleUnitLeftIso_formula]
  apply Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply DFunLike.ext
  intro r
  change Γ(X, U) at r
  apply DFunLike.ext
  intro m
  change (show Γ(X, U) from a.app U r) • m =
    X.presheaf.map U.leTop.op (Global.Sections.moduleSectionHomEquiv (Line.Bundles.structureModule X) a) • (r • m)
  have hres : X.presheaf.map U.leTop.op (Global.Sections.moduleSectionHomEquiv (Line.Bundles.structureModule X) a) =
      (show Γ(X, U) from a.app U (1 : Γ(X, U))) :=
    Section.Gluing.moduleSectionHomEquiv_restrict (Line.Bundles.structureModule X) a U
  have ha : (show Γ(X, U) from a.app U r) = r * (show Γ(X, U) from a.app U (1 : Γ(X, U))) :=
    (congrArg (a.app U) (mul_one r)).symm.trans (a.app_smul r (1 : Γ(X, U)))
  exact (congrArg (fun c : Γ(X, U) => c • m) ha).trans
    ((mul_smul r (show Γ(X, U) from a.app U (1 : Γ(X, U))) m).trans
      ((smul_comm r (show Γ(X, U) from a.app U (1 : Γ(X, U))) m).trans
        (congrArg (fun c : Γ(X, U) => c • (r • m)) hres.symm)))

def moduleSectionFrameIso (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (e : L.sheaf ≅ Line.Bundles.structureModule X) : Tensor.ProductSheaf.tensorModule L.sheaf M ≅ M :=
  Tensor.Bifunctor.tensorModuleMapIso e (Iso.refl M) ≪≫ Tensor.ProductSheaf.tensorModuleUnitLeftIso M

theorem moduleSectionMultiply_frame (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (e : L.sheaf ≅ Line.Bundles.structureModule X) :
    moduleSectionMultiply L M s ≫ (moduleSectionFrameIso L M e).hom =
      Global.ModuleScalars.globalModuleScalar M (Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom)) := by
  change ((Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Tensor.Bifunctor.tensorModuleMap s (𝟙 M)) ≫
    (Tensor.Bifunctor.tensorModuleMap e.hom (𝟙 M) ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom) = _
  calc
    ((Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Tensor.Bifunctor.tensorModuleMap s (𝟙 M)) ≫
        (Tensor.Bifunctor.tensorModuleMap e.hom (𝟙 M) ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom) =
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫
        (Tensor.Bifunctor.tensorModuleMap s (𝟙 M) ≫ Tensor.Bifunctor.tensorModuleMap e.hom (𝟙 M)) ≫
          (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom := by simp only [Category.assoc]
    _ = (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫
        Tensor.Bifunctor.tensorModuleMap (s ≫ e.hom) (𝟙 M) ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom := by
      rw [Tensor.Bifunctor.tensorModuleMap_comp, Category.id_comp]
    _ = Global.ModuleScalars.globalModuleScalar M (Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom)) := by
      rw [tensorModuleUnitLeftIso_scalar]
      simp only [Iso.inv_hom_id_assoc]

theorem moduleSectionMultiply_mono_iff_frame
    (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (e : L.sheaf ≅ Line.Bundles.structureModule X) :
    Mono (moduleSectionMultiply L M s) ↔
      Mono (Global.ModuleScalars.globalModuleScalar M (Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom))) := by
  rw [← moduleSectionMultiply_frame L M s e]
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    refine ⟨fun {Z} f g hfg => ?_⟩
    apply (cancel_mono (moduleSectionMultiply L M s ≫ (moduleSectionFrameIso L M e).hom)).mp
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ (moduleSectionFrameIso L M e).hom) hfg).trans (Category.assoc _ _ _))

theorem moduleSectionMultiply_mono_iff_avoids_associatedPrimes
    [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (L : Line.Bundles.LineBundle X) (M : X.Modules) [M.IsQuasicoherent]
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (e : L.sheaf ≅ Line.Bundles.structureModule X) :
    Mono (moduleSectionMultiply L M s) ↔
      ∀ P ∈ associatedPrimes Γ(X, ⊤) Γ(M, ⊤),
        Frame.Coordinates.structureModuleEndValue X (s ≫ e.hom) ∉ P := by
  rw [moduleSectionMultiply_mono_iff_frame L M s e,
    Affine.ModuleMonomorphisms.affineModuleScalar_mono_iff_avoids_associatedPrimes]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionMultiplication
