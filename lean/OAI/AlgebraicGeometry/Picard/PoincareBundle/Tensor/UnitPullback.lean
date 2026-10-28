import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

/-! # Unit Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

noncomputable section

/-!
# The canonical tensor pullback comparison on the structure sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

theorem homEquiv_map_counit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {M : C} {N : D} (t : M ⟶ R.obj N) :
    a.homEquiv M N (L.map t ≫ a.counit.app N) = t := by
  rw [← a.homEquiv_counit, Equiv.apply_symm_apply]

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

/-- Isomorphic input sheaves give the canonical tensor isomorphism. -/
def tensorIso {X : Scheme.{u}} {M M' N N' : X.Modules} (a : M ≅ M') (b : N ≅ N') :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N' where
  hom := SheafMaps.tensorMap a.hom b.hom
  inv := SheafMaps.tensorMap a.inv b.inv
  hom_inv_id := by rw [SheafMaps.tensorMap_comp, a.hom_inv_id, b.hom_inv_id, SheafMaps.tensorMap_id]
  inv_hom_id := by rw [SheafMaps.tensorMap_comp, a.inv_hom_id, b.inv_hom_id, SheafMaps.tensorMap_id]

instance tensorMap_isIso {X : Scheme.{u}} {M M' N N' : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') [IsIso a] [IsIso b] : IsIso (SheafMaps.tensorMap a b) :=
  (tensorIso (asIso a) (asIso b)).isIso_hom

/-- Multiplication by a section of the structure sheaf is an actual sheaf-bilinear map. -/
def scalarBilinear {X : Scheme.{u}} (M : X.Modules) : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M M where
  app U := LinearMap.lsmul Γ(X, U) Γ(M, U)
  naturality h x y := M.map_smul h x y

/-- The tensor unit isomorphism corresponds to the presheaf unit isomorphism under sheafification. -/
theorem tensorUnitLeft_hom_presheaf {X : Scheme.{u}} (M : X.Modules) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom = (λ_ M.val).hom := by
  change (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ M
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (λ_ M.val).hom ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app M) = _
  exact homEquiv_map_counit (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)) _

/-- The actual tensor unit isomorphism is multiplication of sections. -/
theorem tensorUnitLeft_bilinear {X : Scheme.{u}} (M : X.Modules) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom = scalarBilinear M := by
  change AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorPresheafHomEquiv _ _ _
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom) = _
  rw [tensorUnitLeft_hom_presheaf]
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original structure sheaf maps to the direct image of the pulled-back structure sheaf. -/
def baseUnitMap : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- The actual pullback unit isomorphism is adjoint to the map of structure sheaves. -/
theorem unitIso_homEquiv :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
      baseUnitMap f := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom

/-- The two canonical unit maps agree in their explicit adjunction form. -/
theorem unitIso_unit :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
      (Scheme.Modules.pushforward f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom = baseUnitMap f := by
  have h := unitIso_homEquiv f
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- The map of structure sheaves preserves the scalar multiplication bilinear maps. -/
theorem scalar_pushforward :
    ((scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).pushforward f).precomp (baseUnitMap f) (baseUnitMap f) =
      (scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)).postcomp (baseUnitMap f) := by
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hm := (f.app U).hom.map_mul x y
  exact hm.symm

/-- On structure sheaves, the canonical tensor comparison agrees with the actual unit identifications. -/
theorem pullbackMap_unit_fac :
    PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
      SheafMaps.tensorMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom =
    (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)).hom ≫
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) _).injective
  rw [PullbackMap.pullbackMap_postcomp, SheafMaps.tensorMap_precomp, tensorUnitLeft_bilinear,
    Adjunction.homEquiv_naturality_left, unitIso_homEquiv, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
    tensorUnitLeft_bilinear]
  unfold PullbackMap.bilinearAdjoint
  rw [PullbackMap.pushforward_precomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, unitIso_unit, scalar_pushforward]

/-- The canonical tensor comparison is invertible on the structure sheaf for every scheme morphism. -/
theorem pullbackMap_unit_isIso : IsIso (PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) := by
  let t := SheafMaps.tensorMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom
  have ht : IsIso t := by dsimp only [t]; infer_instance
  have hc : IsIso (PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫ t) := by
    change IsIso (PullbackMap.pullbackMap f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
      SheafMaps.tensorMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom)
    rw [pullbackMap_unit_fac]
    infer_instance
  exact (@isIso_comp_right_iff _ _ _ _ _ _ _ ht).mp hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback
