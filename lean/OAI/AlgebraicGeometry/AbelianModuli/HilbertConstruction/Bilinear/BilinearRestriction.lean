import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

/-! # Bilinear Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear

noncomputable section

/-! Restriction and direct image of bilinear sheaf maps, with their adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Direct image of a bilinear map, with coordinate-ring scalars restricted. -/
def Sheaves.SheafBilinearMap.pushforward {M N P : X.Modules} (β : Sheaves.SheafBilinearMap M N P) (f : X ⟶ Y) :
    Sheaves.SheafBilinearMap ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) ((Scheme.Modules.pushforward f).obj P) where
  app U := {
    toFun x := {
      toFun y := β.app (f ⁻¹ᵁ U) x y
      map_add' y z := (β.app (f ⁻¹ᵁ U) x).map_add y z
      map_smul' r y := (β.app (f ⁻¹ᵁ U) x).map_smul (f.app U r) y }
    map_add' x y := LinearMap.ext fun z =>
      LinearMap.congr_fun ((β.app (f ⁻¹ᵁ U)).map_add x y) z
    map_smul' r x := LinearMap.ext fun z =>
      LinearMap.congr_fun ((β.app (f ⁻¹ᵁ U)).map_smul (f.app U r) x) z }
  naturality h x y := β.naturality ((TopologicalSpace.Opens.map f.base).map h) x y

/-- Restriction of a bilinear map to an open subscheme. -/
def Sheaves.SheafBilinearMap.restrict {M N P : Y.Modules} (β : Sheaves.SheafBilinearMap M N P) (f : X ⟶ Y)
    [IsOpenImmersion f] : Sheaves.SheafBilinearMap (M.restrict f) (N.restrict f) (P.restrict f) where
  app U := {
    toFun x := {
      toFun y := β.app (f ''ᵁ U) x y
      map_add' y z := (β.app (f ''ᵁ U) x).map_add y z
      map_smul' r y := (β.app (f ''ᵁ U) x).map_smul ((f.appIso U).inv r) y }
    map_add' x y := LinearMap.ext fun z =>
      LinearMap.congr_fun ((β.app (f ''ᵁ U)).map_add x y) z
    map_smul' r x := LinearMap.ext fun z =>
      LinearMap.congr_fun ((β.app (f ''ᵁ U)).map_smul ((f.appIso U).inv r) x) z }
  naturality h x y := β.naturality (f.opensFunctor.map h) x y

theorem Sheaves.SheafBilinearMap.precomp_comp {M M' M'' N N' N'' P : X.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : M' ⟶ M) (g : N' ⟶ N) (f' : M'' ⟶ M') (g' : N'' ⟶ N') :
    (β.precomp f g).precomp f' g' = β.precomp (f' ≫ f) (g' ≫ g) := by
  ext U x y
  rfl

theorem Sheaves.SheafBilinearMap.pushforward_postcomp {M N P Q : X.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) (h : P ⟶ Q) :
    (β.postcomp h).pushforward f =
      (β.pushforward f).postcomp ((Scheme.Modules.pushforward f).map h) := by
  ext U x y
  rfl

theorem Sheaves.SheafBilinearMap.restrict_postcomp {M N P Q : Y.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) [IsOpenImmersion f] (h : P ⟶ Q) :
    (β.postcomp h).restrict f =
      (β.restrict f).postcomp ((Scheme.Modules.restrictFunctor f).map h) := by
  ext U x y
  rfl

theorem Sheaves.SheafBilinearMap.restrict_precomp {M M' N N' P : Y.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) [IsOpenImmersion f] (a : M' ⟶ M) (b : N' ⟶ N) :
    (β.precomp a b).restrict f = (β.restrict f).precomp
      ((Scheme.Modules.restrictFunctor f).map a) ((Scheme.Modules.restrictFunctor f).map b) := by
  ext U x y
  rfl

theorem Sheaves.SheafBilinearMap.restrict_unit_naturality {M N P : Y.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ((β.restrict f).pushforward f).precomp
        ((Scheme.Modules.restrictAdjunction f).unit.app M)
        ((Scheme.Modules.restrictAdjunction f).unit.app N) =
      β.postcomp ((Scheme.Modules.restrictAdjunction f).unit.app P) := by
  ext U x y
  exact (β.naturality (f.isOpenEmbedding.isOpenMap.adjunction.counit.app U) x y).symm

theorem Sheaves.SheafBilinearMap.restrict_counit_naturality {M N P : X.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ((β.pushforward f).restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app P) =
      β.precomp ((Scheme.Modules.restrictAdjunction f).counit.app M)
        ((Scheme.Modules.restrictAdjunction f).counit.app N) := by
  ext U x y
  exact β.naturality (f.isOpenEmbedding.isOpenMap.adjunction.unit.app U) x y

/-- The restriction/direct-image adjunction for bilinear maps. -/
def Sheaves.SheafBilinearMap.restrictHomEquiv (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) (P : X.Modules) :
    Sheaves.SheafBilinearMap (M.restrict f) (N.restrict f) P ≃
      Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P) where
  toFun β := (β.pushforward f).precomp ((Scheme.Modules.restrictAdjunction f).unit.app M)
    ((Scheme.Modules.restrictAdjunction f).unit.app N)
  invFun β := (β.restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app P)
  left_inv β := by
    change (((β.pushforward f).precomp ((Scheme.Modules.restrictAdjunction f).unit.app M)
      ((Scheme.Modules.restrictAdjunction f).unit.app N)).restrict f).postcomp
        ((Scheme.Modules.restrictAdjunction f).counit.app P) = β
    rw [Sheaves.SheafBilinearMap.restrict_precomp, ← Sheaves.SheafBilinearMap.precomp_postcomp, Sheaves.SheafBilinearMap.restrict_counit_naturality, Sheaves.SheafBilinearMap.precomp_comp]
    exact (congrArg₂ (fun a b => β.precomp a b)
      ((Scheme.Modules.restrictAdjunction f).left_triangle_components M)
      ((Scheme.Modules.restrictAdjunction f).left_triangle_components N)).trans β.precomp_id
  right_inv β := by
    change (((β.restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app P)).pushforward f).precomp
      ((Scheme.Modules.restrictAdjunction f).unit.app M)
        ((Scheme.Modules.restrictAdjunction f).unit.app N) = β
    rw [Sheaves.SheafBilinearMap.pushforward_postcomp, Sheaves.SheafBilinearMap.precomp_postcomp, Sheaves.SheafBilinearMap.restrict_unit_naturality, ← Sheaves.SheafBilinearMap.postcomp_comp]
    exact (congrArg (fun h => β.postcomp h)
      ((Scheme.Modules.restrictAdjunction f).right_triangle_components P)).trans β.postcomp_id

/-- Naturality of the bilinear adjunction in its output sheaf. -/
theorem Sheaves.SheafBilinearMap.restrictHomEquiv_postcomp (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)
    {P Q : X.Modules} (β : Sheaves.SheafBilinearMap (M.restrict f) (N.restrict f) P) (h : P ⟶ Q) :
    Sheaves.SheafBilinearMap.restrictHomEquiv f M N Q (β.postcomp h) =
      (Sheaves.SheafBilinearMap.restrictHomEquiv f M N P β).postcomp ((Scheme.Modules.pushforward f).map h) := by
  change ((β.postcomp h).pushforward f).precomp _ _ = _
  rw [Sheaves.SheafBilinearMap.pushforward_postcomp, Sheaves.SheafBilinearMap.precomp_postcomp]
  rfl

/-- Naturality of the inverse bilinear adjunction in its output sheaf. -/
theorem Sheaves.SheafBilinearMap.restrictHomEquiv_symm_postcomp (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)
    {P Q : X.Modules} (β : Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P))
    (h : P ⟶ Q) :
    (Sheaves.SheafBilinearMap.restrictHomEquiv f M N Q).symm (β.postcomp ((Scheme.Modules.pushforward f).map h)) =
      ((Sheaves.SheafBilinearMap.restrictHomEquiv f M N P).symm β).postcomp h := by
  apply (Sheaves.SheafBilinearMap.restrictHomEquiv f M N Q).injective
  rw [Equiv.apply_symm_apply, Sheaves.SheafBilinearMap.restrictHomEquiv_postcomp, Equiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear
