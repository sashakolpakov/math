import OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionTransformation

/-! # Adjunction Resolution Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionAugmentation.AdjunctionResolutionPullback

noncomputable section

/-! The inverse-image mate of an actual direct-image resolution comparison preserves augmentation. -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)

theorem single_homEquiv (P : C) :
    (AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj (.up ℕ)).homEquiv _ _
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).hom.app P) =
      (CochainComplex.single₀ C).map (adj.unit.app P) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app (F.obj P) := by
  let A := AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj (.up ℕ)
  let s := (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).hom.app P
  have hs := A.homEquiv_unit _ _ s
  apply HomologicalComplex.from_single_hom_ext
  refine (congrArg (fun k => k.f 0) hs).trans ?_
  simp [A, s, AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes, HomologicalComplex.singleMapHomologicalComplex]
  change adj.unit.app P ≫ G.map (𝟙 (F.obj P)) = adj.unit.app P
  rw [G.map_id]
  exact Category.comp_id (adj.unit.app P)

variable (T : C ⥤ CochainComplex C ℕ) (N : D ⥤ CochainComplex D ℕ)
  (e : G ⋙ T ≅ N ⋙ G.mapHomologicalComplex (.up ℕ))
  (η : CochainComplex.single₀ C ⟶ T) (θ : CochainComplex.single₀ D ⟶ N)
  (h : ∀ P, η.app (G.obj P) ≫ e.hom.app P =
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app P ≫
      (G.mapHomologicalComplex (.up ℕ)).map (θ.app P))

include h in
theorem augmentation (P : C) :
    (F.mapHomologicalComplex (.up ℕ)).map (η.app P) ≫ AdjunctionResolutionTransformation.AdjunctionResolutionPullback.map adj T N e P =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).hom.app P ≫ θ.app (F.obj P) := by
  let A := AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj (.up ℕ)
  let s := (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).hom.app P
  have hd : η.app P ≫ AdjunctionResolutionTransformation.AdjunctionResolutionPullback.directMap adj T N e P =
      ((CochainComplex.single₀ C).map (adj.unit.app P) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℕ) 0).inv.app (F.obj P)) ≫
          (G.mapHomologicalComplex (.up ℕ)).map (θ.app (F.obj P)) :=
    ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ (η.naturality (adj.unit.app P)).symm (h (F.obj P))
  have hs : η.app P ≫ AdjunctionResolutionTransformation.AdjunctionResolutionPullback.directMap adj T N e P = A.homEquiv _ _ s ≫
      (G.mapHomologicalComplex (.up ℕ)).map (θ.app (F.obj P)) :=
    hd.trans (congrArg (fun k => k ≫ (G.mapHomologicalComplex (.up ℕ)).map (θ.app (F.obj P)))
      (single_homEquiv adj P).symm)
  have hm := A.homEquiv_naturality_right_square (η.app P) (AdjunctionResolutionTransformation.AdjunctionResolutionPullback.directMap adj T N e P)
    (A.homEquiv _ _ s) (θ.app (F.obj P)) hs
  dsimp only [AdjunctionResolutionTransformation.AdjunctionResolutionPullback.map]
  exact hm.trans (congrArg (fun k => k ≫ θ.app (F.obj P)) ((A.homEquiv _ _).symm_apply_apply s))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionAugmentation.AdjunctionResolutionPullback
