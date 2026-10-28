import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Isomorphisms

/-! # Multilinear Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Restriction of multilinear maps of module sheaves to an open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M N : Y.Modules} {n : ℕ}

/-- Direct image of a multilinear map, with scalars restricted along the
map on coordinate rings. -/
def Tensor.Powers.SheafMultilinearMap.pushforward {P Q : X.Modules} (β : Tensor.Powers.SheafMultilinearMap P n Q) (f : X ⟶ Y) :
    Tensor.Powers.SheafMultilinearMap ((Scheme.Modules.pushforward f).obj P) n
      ((Scheme.Modules.pushforward f).obj Q) where
  app U := {
    toFun := (β.app (f ⁻¹ᵁ U)).toFun
    map_update_add' s i x y := (β.app (f ⁻¹ᵁ U)).map_update_add s i x y
    map_update_smul' s i r x := (β.app (f ⁻¹ᵁ U)).map_update_smul s i (f.app U r) x }
  naturality h s := β.naturality ((TopologicalSpace.Opens.map f.base).map h) s

theorem Tensor.Powers.SheafMultilinearMap.pushforward_postcomp {P Q R : X.Modules} (β : Tensor.Powers.SheafMultilinearMap P n Q)
    (f : X ⟶ Y) (h : Q ⟶ R) :
    (β.postcomp h).pushforward f =
      (β.pushforward f).postcomp ((Scheme.Modules.pushforward f).map h) := by
  ext U s
  rfl

theorem Tensor.Powers.SheafMultilinearMap.pushforward_precomp {P Q R : X.Modules} (β : Tensor.Powers.SheafMultilinearMap P n Q)
    (f : X ⟶ Y) (h : R ⟶ P) :
    (β.precomp h).pushforward f =
      (β.pushforward f).precomp ((Scheme.Modules.pushforward f).map h) := by
  ext U s
  rfl

/-- Restrict a multilinear map along an open immersion. The section formula
uses the corresponding image open and the isomorphism of its coordinate rings. -/
def Tensor.Powers.SheafMultilinearMap.restrict (β : Tensor.Powers.SheafMultilinearMap L n M) (f : X ⟶ Y) [IsOpenImmersion f] :
    Tensor.Powers.SheafMultilinearMap (L.restrict f) n (M.restrict f) where
  app U := {
    toFun := (β.app (f ''ᵁ U)).toFun
    map_update_add' s i x y := (β.app (f ''ᵁ U)).map_update_add s i x y
    map_update_smul' s i r x := (β.app (f ''ᵁ U)).map_update_smul s i ((f.appIso U).inv r) x }
  naturality h s := β.naturality (f.opensFunctor.map h) s

/-- Restriction commutes with postcomposition by a morphism of module sheaves. -/
theorem Tensor.Powers.SheafMultilinearMap.restrict_postcomp (β : Tensor.Powers.SheafMultilinearMap L n M) (f : X ⟶ Y) [IsOpenImmersion f]
    (h : M ⟶ N) :
    (β.postcomp h).restrict f = (β.restrict f).postcomp ((Scheme.Modules.restrictFunctor f).map h) := by
  ext U s
  rfl

/-- Restriction commutes with precomposition in all the multilinear arguments. -/
theorem Tensor.Powers.SheafMultilinearMap.restrict_precomp (β : Tensor.Powers.SheafMultilinearMap L n M) (f : X ⟶ Y) [IsOpenImmersion f]
    (h : N ⟶ L) :
    (β.precomp h).restrict f = (β.restrict f).precomp ((Scheme.Modules.restrictFunctor f).map h) := by
  ext U s
  rfl

/-- The unit of restriction/direct image is compatible with multilinear maps. -/
theorem Tensor.Powers.SheafMultilinearMap.restrict_unit_naturality (β : Tensor.Powers.SheafMultilinearMap L n M)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ((β.restrict f).pushforward f).precomp ((Scheme.Modules.restrictAdjunction f).unit.app L) =
      β.postcomp ((Scheme.Modules.restrictAdjunction f).unit.app M) := by
  ext U s
  exact (β.naturality (f.isOpenEmbedding.isOpenMap.adjunction.counit.app U) s).symm

/-- The counit of restriction/direct image is compatible with multilinear maps. -/
theorem Tensor.Powers.SheafMultilinearMap.restrict_counit_naturality {P Q : X.Modules} (β : Tensor.Powers.SheafMultilinearMap P n Q)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ((β.pushforward f).restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app Q) =
      β.precomp ((Scheme.Modules.restrictAdjunction f).counit.app P) := by
  ext U s
  exact β.naturality (f.isOpenEmbedding.isOpenMap.adjunction.unit.app U) s

/-- The restriction/direct-image adjunction also holds for multilinear maps. -/
def Tensor.Powers.SheafMultilinearMap.restrictHomEquiv (f : X ⟶ Y) [IsOpenImmersion f] (L : Y.Modules) (n : ℕ) (Q : X.Modules) :
    Tensor.Powers.SheafMultilinearMap (L.restrict f) n Q ≃
      Tensor.Powers.SheafMultilinearMap L n ((Scheme.Modules.pushforward f).obj Q) where
  toFun β := (β.pushforward f).precomp ((Scheme.Modules.restrictAdjunction f).unit.app L)
  invFun β := (β.restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app Q)
  left_inv β := by
    change (((β.pushforward f).precomp
      ((Scheme.Modules.restrictAdjunction f).unit.app L)).restrict f).postcomp
        ((Scheme.Modules.restrictAdjunction f).counit.app Q) = β
    rw [Tensor.Powers.SheafMultilinearMap.restrict_precomp, ← Tensor.Powers.SheafMultilinearMap.precomp_postcomp, Tensor.Powers.SheafMultilinearMap.restrict_counit_naturality, Tensor.Powers.SheafMultilinearMap.precomp_comp]
    exact (congrArg (fun h => β.precomp h)
      ((Scheme.Modules.restrictAdjunction f).left_triangle_components L)).trans β.precomp_id
  right_inv β := by
    change (((β.restrict f).postcomp
      ((Scheme.Modules.restrictAdjunction f).counit.app Q)).pushforward f).precomp
        ((Scheme.Modules.restrictAdjunction f).unit.app L) = β
    rw [Tensor.Powers.SheafMultilinearMap.pushforward_postcomp, Tensor.Powers.SheafMultilinearMap.precomp_postcomp, Tensor.Powers.SheafMultilinearMap.restrict_unit_naturality, ← Tensor.Powers.SheafMultilinearMap.postcomp_comp]
    exact (congrArg (fun h => β.postcomp h)
      ((Scheme.Modules.restrictAdjunction f).right_triangle_components Q)).trans β.postcomp_id

/-- The multilinear adjunction respects postcomposition by a restricted sheaf map. -/
theorem Tensor.Powers.SheafMultilinearMap.restrictHomEquiv_postcomp (β : Tensor.Powers.SheafMultilinearMap L n M)
    (f : X ⟶ Y) [IsOpenImmersion f] {Q : X.Modules} (h : M.restrict f ⟶ Q) :
    Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n Q ((β.restrict f).postcomp h) =
      β.postcomp ((Scheme.Modules.restrictAdjunction f).homEquiv M Q h) := by
  change (((β.restrict f).postcomp h).pushforward f).precomp
    ((Scheme.Modules.restrictAdjunction f).unit.app L) = _
  rw [Tensor.Powers.SheafMultilinearMap.pushforward_postcomp, Tensor.Powers.SheafMultilinearMap.precomp_postcomp, Tensor.Powers.SheafMultilinearMap.restrict_unit_naturality, ← Tensor.Powers.SheafMultilinearMap.postcomp_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
