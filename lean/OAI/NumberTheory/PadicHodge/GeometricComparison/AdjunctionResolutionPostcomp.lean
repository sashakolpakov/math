import OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionTransformation

/-! # Adjunction Resolution Postcomp -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionPostcomp.AdjunctionResolutionPullback

noncomputable section

/-! The actual inverse-image resolution mate intertwines postcomposition with the original direct-image adjoint. -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
  (T : C ⥤ CochainComplex C ℕ) (N : D ⥤ CochainComplex D ℕ)
  (e : G ⋙ T ≅ N ⋙ G.mapHomologicalComplex (.up ℕ))

theorem map_postcomp (P : C) (Q : D) (b : F.obj P ⟶ Q) :
    (AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj (.up ℕ)).homEquiv _ _ (AdjunctionResolutionTransformation.AdjunctionResolutionPullback.map adj T N e P ≫ N.map b) =
      T.map (adj.homEquiv P Q b) ≫ e.hom.app Q := by
  let A := AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj (.up ℕ)
  let Gc := G.mapHomologicalComplex (.up ℕ)
  have hm : A.homEquiv _ _ (AdjunctionResolutionTransformation.AdjunctionResolutionPullback.map adj T N e P) = AdjunctionResolutionTransformation.AdjunctionResolutionPullback.directMap adj T N e P :=
    (A.homEquiv _ _).apply_symm_apply _
  have hT : T.map (adj.unit.app P) ≫ T.map (G.map b) = T.map (adj.homEquiv P Q b) :=
    (T.map_comp _ _).symm.trans (congrArg T.map (adj.homEquiv_unit P Q b).symm)
  exact (A.homEquiv_naturality_right (AdjunctionResolutionTransformation.AdjunctionResolutionPullback.map adj T N e P) (N.map b)).trans
    ((congrArg (fun k => k ≫ Gc.map (N.map b)) hm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => T.map (adj.unit.app P) ≫ k) (e.hom.naturality b).symm).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ e.hom.app Q) hT)))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionPostcomp.AdjunctionResolutionPullback
