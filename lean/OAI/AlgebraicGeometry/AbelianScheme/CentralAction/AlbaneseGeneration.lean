import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ProductGeneration

/-! # Albanese Generation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseGeneration

noncomputable section

/-! IntegralModel's actual geometric generation on every component determines
additive endomorphisms of the full product Albanese point group. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace Construction

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

theorem albanesePointCoordinates_aPoint_single
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    (T : Over (Spec (.of K))) (j : Fin D.componentCount)
    (x : T ⟶ D.componentGeneric j) :
    AlbaneseCoordinates.Construction.albanesePointCoordinates D T (D.aPoint hgeometry j x) =
      Pi.single j (Additive.ofMul (TateComparison.Subgroup.pullbackPointsEquiv (D.components.S j) D.generic T x ≫
        D.components.a j)) := by
  classical
  funext k
  rw [AlbaneseCoordinates.Construction.albanesePointCoordinates_aPoint]
  by_cases h : j = k
  · subst k
    simp only [PELModuli.IntegralModel.Components.ComponentAlbaneseData.coordinateMap_self, Pi.single_eq_same]
  · rw [D.components.coordinateMap_ne j k h, Pi.single_eq_of_ne (Ne.symm h), MonObj.comp_one]
    rfl

theorem albanese_point_end_eq_of_differences
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q) (hgeometry : D.HasIntegralModelGeometry)
    {k : Type} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K))
    (F : Additive (Over.mk b ⟶ D.albaneseGroup.X) →+
      Additive (Over.mk b ⟶ D.albaneseGroup.X))
    (hF : ∀ (j : Fin D.componentCount) (x y : Over.mk b ⟶ D.componentGeneric j),
      F (D.aPoint hgeometry j x - D.aPoint hgeometry j y) =
        D.aPoint hgeometry j x - D.aPoint hgeometry j y) :
    ∀ z, F z = z := by
  classical
  let T := Over.mk b
  let t : PELModuli.IntegralModel.Base.GeometricPoint (TateComparison.Data.modelBase K D.denominator) :=
    { field := k, morphism := b ≫ D.generic }
  let a (j : Fin D.componentCount) (x : (Over.map D.generic).obj T ⟶ D.components.S j) :=
    Additive.ofMul (x ≫ D.components.a j)
  let z (j : Fin D.componentCount) (x : (Over.map D.generic).obj T ⟶ D.components.S j) :=
    D.aPoint hgeometry j ((TateComparison.Subgroup.pullbackPointsEquiv (D.components.S j) D.generic T).symm x)
  refine ProductGeneration.Construction.end_eq_id_of_component_differences (AlbaneseCoordinates.Construction.albanesePointCoordinates D T) a z ?_ ?_ F ?_
  · intro j x
    change AlbaneseCoordinates.Construction.albanesePointCoordinates D T (D.aPoint hgeometry j _) = _
    rw [albanesePointCoordinates_aPoint_single, Equiv.apply_symm_apply]
  · intro j
    obtain ⟨n, _, hn⟩ := hgeometry.generation j
    exact ⟨n, hn t⟩
  · intro j x y
    exact hF j _ _

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.AlbaneseGeneration
