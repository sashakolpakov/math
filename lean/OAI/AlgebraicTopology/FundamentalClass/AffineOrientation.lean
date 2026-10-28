import OAI.AlgebraicTopology.FundamentalClass.SimplexSupport

/-! # Affine Orientation -/

namespace OAI.AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction

noncomputable section

section

/-! Positive affine rescaling preserves the geometric local orientation
classes. The proof uses a homotopy of punctured Euclidean spaces. -/

open _root_.CategoryTheory Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Scale

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

def positiveScale (r : ℝ) : TopCat.of E ⟶ TopCat.of E :=
  TopCat.ofHom ⟨fun x => r • x, continuous_const.smul continuous_id⟩

theorem positiveScale_mapsTo (r : ℝ) (hr : 0 < r) :
    MapsTo (positiveScale E r) ({0}ᶜ : Set E) ({0}ᶜ : Set E) := by
  intro x hx
  change r • x ≠ 0
  exact smul_ne_zero hr.ne' hx

def positiveScaleHomotopy (r : ℝ) :
    TopCat.Homotopy (𝟙 (TopCat.of E)) (positiveScale E r) where
  toFun z := (1 - (z.1 : ℝ) + (z.1 : ℝ) * r) • z.2
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp [positiveScale]

theorem positiveScaleHomotopy_mapsTo (r : ℝ) (hr : 0 < r) (t : unitInterval) :
    MapsTo (fun x => positiveScaleHomotopy E r (t, x)) ({0}ᶜ : Set E) ({0}ᶜ : Set E) := by
  intro x hx
  have hp : 0 < 1 - (t : ℝ) + (t : ℝ) * r := by
    rcases t.property.1.eq_or_lt with ht | ht
    · rw [← ht]
      norm_num
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2) (mul_pos ht hr)
  exact smul_ne_zero hp.ne' hx

theorem positiveScaleHomologyMap_eq_id (r : ℝ) (hr : 0 < r) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (positiveScale E r) (positiveScale_mapsTo E r hr) n =
      𝟙 (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of E) 0 n) := by
  have h := AlgebraicGeometry.CycleClass.Geometric.RelativeHomotopy.Cycles.relativeSingularHomologyMap_eq_of_homotopy
    (X := TopCat.of E) (Y := TopCat.of E)
    (A := ({0}ᶜ : Set E)) (B := ({0}ᶜ : Set E))
    (fun _ hx => hx) (positiveScale_mapsTo E r hr) (positiveScaleHomotopy E r)
    (positiveScaleHomotopy_mapsTo E r hr) n
  rw [AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_id] at h
  exact h.symm

def positiveAffine (a : E) (r : ℝ) : TopCat.of E ⟶ TopCat.of E :=
  TopCat.ofHom ⟨fun x => a + r • x, continuous_const.add (continuous_const.smul continuous_id)⟩

theorem positiveAffine_injective (a : E) (r : ℝ) (hr : 0 < r) :
    Function.Injective (positiveAffine E a r) := by
  intro x y h
  exact (smul_right_injective E hr.ne') (add_left_cancel h)

theorem positiveAffine_mapsTo_point (a : E) (r : ℝ) (hr : 0 < r) (x : E) :
    MapsTo (positiveAffine E a r) ({x}ᶜ : Set E)
      ({positiveAffine E a r x}ᶜ : Set E) := by
  intro y hy h
  exact hy (positiveAffine_injective E a r hr h)

theorem positiveAffine_translation (a : E) (r : ℝ) (hr : 0 < r) (x : E) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (positiveAffine E a r) (positiveAffine_mapsTo_point E a r hr x) n ≫
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso E (positiveAffine E a r x) n).hom =
      (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso E x n).hom := by
  let tx := (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E) (Homeomorph.subRight x)).hom
  let ty := (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E)
    (Homeomorph.subRight (positiveAffine E a r x))).hom
  have hx : MapsTo tx ({x}ᶜ : Set E) ({0}ᶜ : Set E) := by
    intro y hy
    exact sub_ne_zero.mpr hy
  have hy : MapsTo ty ({positiveAffine E a r x}ᶜ : Set E) ({0}ᶜ : Set E) := by
    intro y hy
    exact sub_ne_zero.mpr hy
  have hmap : positiveAffine E a r ≫ ty = tx ≫ positiveScale E r := by
    ext y
    change a + r • y - (a + r • x) = r • (y - x)
    simp only [smul_sub]
    abel
  change AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (positiveAffine E a r) _ n ≫
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap ty hy n = AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap tx hx n
  calc
    _ = AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap tx hx n ≫
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (positiveScale E r) (positiveScale_mapsTo E r hr) n := by
      rw [AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp]
      congr 1
    _ = _ := by rw [positiveScaleHomologyMap_eq_id E r hr n, Category.comp_id]

end Scale

theorem positiveCoordinateClass_affine (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r)
    (x : Fin d → ℝ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (positiveAffine (Fin d → ℝ) a r)
      (positiveAffine_mapsTo_point (Fin d → ℝ) a r hr x) d (IntegrationOrientation.Geometry.positiveCoordinateClass d x) =
      IntegrationOrientation.Geometry.positiveCoordinateClass d (positiveAffine (Fin d → ℝ) a r x) := by
  apply (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) (positiveAffine (Fin d → ℝ) a r x) d).toLinearEquiv.injective
  have h := ConcreteCategory.congr_hom
    (positiveAffine_translation (Fin d → ℝ) a r hr x d) (IntegrationOrientation.Geometry.positiveCoordinateClass d x)
  exact h.trans (by simp [IntegrationOrientation.Geometry.positiveCoordinateClass])

end

open _root_.CategoryTheory Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def affineInterior (d : ℕ) (a : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  positiveAffine (Fin d → ℝ) a r '' SimplexGeometry.IntegrationConstruction.positiveInterior d

theorem positiveAffine_mapsTo_complement (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r) :
    MapsTo (positiveAffine (Fin d → ℝ) a r) (SimplexGeometry.IntegrationConstruction.positiveInterior d)ᶜ (affineInterior d a r)ᶜ := by
  intro x hx
  rintro ⟨y, hy, h⟩
  exact hx ((positiveAffine_injective (Fin d → ℝ) a r hr h) ▸ hy)

def affineInteriorClass (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r) :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ)) (affineInterior d a r) d :=
  AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (positiveAffine (Fin d → ℝ) a r)
    (positiveAffine_mapsTo_complement d a r hr) d (SimplexSupport.IntegrationConstruction.positiveInteriorClass d)

theorem affineInteriorClass_atPoint (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r)
    (y : Fin d → ℝ) (hy : y ∈ affineInterior d a r) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (affineInterior d a r) y hy d
      (affineInteriorClass d a r hr) = IntegrationOrientation.Geometry.positiveCoordinateClass d y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hcomm :
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (positiveAffine (Fin d → ℝ) a r)
        (positiveAffine_mapsTo_complement d a r hr) d ≫
      AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (affineInterior d a r)
        (positiveAffine (Fin d → ℝ) a r x) ⟨x, hx, rfl⟩ d =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (SimplexGeometry.IntegrationConstruction.positiveInterior d) x hx d ≫
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (positiveAffine (Fin d → ℝ) a r)
        (positiveAffine_mapsTo_point (Fin d → ℝ) a r hr x) d := by
    change AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap _ _ d ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 _) _ d =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap (𝟙 _) _ d ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap _ _ d
    rw [AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp]
    simp only [Category.comp_id, Category.id_comp]
  have h := ConcreteCategory.congr_hom hcomm (SimplexSupport.IntegrationConstruction.positiveInteriorClass d)
  change AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint _ _ _ _ d (affineInteriorClass d a r hr) =
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap _ _ d
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint _ _ x hx d (SimplexSupport.IntegrationConstruction.positiveInteriorClass d)) at h
  rw [SimplexSupport.IntegrationConstruction.positiveInteriorClass_atPoint, positiveCoordinateClass_affine d a r hr x] at h
  exact h

theorem affineInteriorClass_restrict_compact (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKs : K ⊆ affineInterior d a r) :
    AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of (Fin d → ℝ)) hKs d (affineInteriorClass d a r hr) =
      IntegrationOrientation.Geometry.coordinateCompactClass d K hK := by
  apply RealSupport.IntegrationGeometry.realManifold_compactSupport_point_ext d K hK
  intro x hx
  rw [AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint_apply, affineInteriorClass_atPoint,
    IntegrationOrientation.Geometry.coordinateCompactClass_atPoint]

end

end OAI.AlgebraicTopology.FundamentalClass.AffineOrientation.IntegrationConstruction
