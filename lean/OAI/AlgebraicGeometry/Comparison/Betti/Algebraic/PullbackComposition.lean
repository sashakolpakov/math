import OAI.AlgebraicGeometry.Comparison.Betti.PullbackComposition

/-! # Pullback Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.PullbackComposition

noncomputable section

/-! Composition of the original algebraic sheaf-complex pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Sheaves.sectionAlgebra

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem sectionPullback_comp (U : Z.left.Opens) :
    (Sheaves.sectionPullback f (g.left ⁻¹ᵁ U)).comp (Sheaves.sectionPullback g U) = Sheaves.sectionPullback (f ≫ g) U := by
  ext a
  rfl

theorem deRhamPresheafPullback_comp (U : Z.left.Opensᵒᵖ) :
    (Sheaves.deRhamPresheafPullback g).app U ≫
        (Sheaves.deRhamPresheafPullback f).app ((Opens.map g.left.base).op.obj U) =
      (Sheaves.deRhamPresheafPullback (f ≫ g)).app U := by
  change Forms.complexPullback (Sheaves.sectionPullback g U.unop) ≫
      Forms.complexPullback (Sheaves.sectionPullback f (g.left ⁻¹ᵁ U.unop)) = _
  rw [← Forms.complexPullback_comp, sectionPullback_comp]
  rfl

theorem presheafComplexPullbackInt_comp :
    OpenForms.presheafComplexPullbackInt g ≫
        ((Sheaf.CochainPullback.directImagePresheaf g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (OpenForms.presheafComplexPullbackInt f) = OpenForms.presheafComplexPullbackInt (f ≫ g) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  have h := congrArg (fun p => (HomologicalComplex.extendMap p (ComplexShape.embeddingUpIntGE 0)).f i)
    (deRhamPresheafPullback_comp f g U)
  rw [HomologicalComplex.extendMap_comp] at h
  exact h

theorem deRhamSheafDirectImageInt_unit {T V : Over Foundations.Scheme.ProjectiveSpace.complexBase} (k : T ⟶ V) :
    (OpenForms.sheafificationComplexAdjunctionInt V).unit.app (Sheaves.deRhamPresheafComplexInt V) ≫
        ((sheafToPresheaf (Opens.grothendieckTopology V.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (OpenForms.deRhamSheafDirectImageInt k) =
      OpenForms.presheafToDirectImageSheafComplexInt k := by
  have h := ((OpenForms.sheafificationComplexAdjunctionInt V).homEquiv (Sheaves.deRhamPresheafComplexInt V)
    (((Sheaves.directImage k).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (Sheaves.algebraicDeRhamSheafComplexInt T))).apply_symm_apply (OpenForms.presheafToDirectImageSheafComplexInt k)
  exact h

theorem deRhamSheafDirectImageInt_comp :
    OpenForms.deRhamSheafDirectImageInt g ≫
        ((Sheaves.directImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map (OpenForms.deRhamSheafDirectImageInt f) =
      OpenForms.deRhamSheafDirectImageInt (f ≫ g) := by
  let UZ := (sheafToPresheaf (Opens.grothendieckTopology Z.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let UY := (sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let Dg := (Sheaf.CochainPullback.directImagePresheaf g).mapHomologicalComplex (ComplexShape.up ℤ)
  let Df := (Sheaf.CochainPullback.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℤ)
  let Gg := (Sheaves.directImage g).mapHomologicalComplex (ComplexShape.up ℤ)
  let ηX := (OpenForms.sheafificationComplexAdjunctionInt X).unit.app (Sheaves.deRhamPresheafComplexInt X)
  let ηY := (OpenForms.sheafificationComplexAdjunctionInt Y).unit.app (Sheaves.deRhamPresheafComplexInt Y)
  let ηZ := (OpenForms.sheafificationComplexAdjunctionInt Z).unit.app (Sheaves.deRhamPresheafComplexInt Z)
  let pg := OpenForms.presheafComplexPullbackInt g
  let pf := OpenForms.presheafComplexPullbackInt f
  let pfg := OpenForms.presheafComplexPullbackInt (f ≫ g)
  let dg := OpenForms.deRhamSheafDirectImageInt g
  let df := OpenForms.deRhamSheafDirectImageInt f
  let dfg := OpenForms.deRhamSheafDirectImageInt (f ≫ g)
  have hg : ηZ ≫ UZ.map dg = pg ≫ Dg.map ηY := deRhamSheafDirectImageInt_unit g
  have hf : ηY ≫ UY.map df = pf ≫ Df.map ηX := deRhamSheafDirectImageInt_unit f
  have hfg : ηZ ≫ UZ.map dfg = pfg ≫ Dg.map (Df.map ηX) := deRhamSheafDirectImageInt_unit (f ≫ g)
  have hp : pg ≫ Dg.map pf = pfg := presheafComplexPullbackInt_comp f g
  apply ((OpenForms.sheafificationComplexAdjunctionInt Z).homEquiv (Sheaves.deRhamPresheafComplexInt Z)
    (((Sheaves.directImage (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (Sheaves.algebraicDeRhamSheafComplexInt X))).injective
  change ηZ ≫ UZ.map (dg ≫ Gg.map df) = ηZ ≫ UZ.map dfg
  erw [UZ.map_comp dg (Gg.map df), ← Category.assoc, hg, hfg]
  change (pg ≫ Dg.map ηY) ≫ Dg.map (UY.map df) = pfg ≫ Dg.map (Df.map ηX)
  erw [Category.assoc, ← Dg.map_comp, hf, Dg.map_comp, ← Category.assoc, hp]
  rfl

theorem deRhamSheafPullbackInt_normalization {T V : Over Foundations.Scheme.ProjectiveSpace.complexBase} (k : T ⟶ V) :
    (OpenForms.imageComplexAdjunctionInt k).homEquiv (Sheaves.algebraicDeRhamSheafComplexInt V)
      (Sheaves.algebraicDeRhamSheafComplexInt T) (OpenForms.deRhamSheafPullbackInt k) = OpenForms.deRhamSheafDirectImageInt k :=
  ((OpenForms.imageComplexAdjunctionInt k).homEquiv (Sheaves.algebraicDeRhamSheafComplexInt V)
    (Sheaves.algebraicDeRhamSheafComplexInt T)).apply_symm_apply (OpenForms.deRhamSheafDirectImageInt k)

theorem deRhamSheafPullbackInt_comp :
    ((Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map (OpenForms.deRhamSheafPullbackInt g) ≫
        OpenForms.deRhamSheafPullbackInt f =
      (PullbackComposition.inverseImageComplexCompIso f g).hom.app (Sheaves.algebraicDeRhamSheafComplexInt Z) ≫
        OpenForms.deRhamSheafPullbackInt (f ≫ g) := by
  apply (((OpenForms.imageComplexAdjunctionInt g).comp (OpenForms.imageComplexAdjunctionInt f)).homEquiv
    (Sheaves.algebraicDeRhamSheafComplexInt Z) (Sheaves.algebraicDeRhamSheafComplexInt X)).injective
  have hl := AdjunctionComplexUniqueness.comp_homEquiv_map_comp (OpenForms.imageComplexAdjunctionInt g)
    (OpenForms.imageComplexAdjunctionInt f) (OpenForms.deRhamSheafPullbackInt g) (OpenForms.deRhamSheafPullbackInt f)
  erw [deRhamSheafPullbackInt_normalization g, deRhamSheafPullbackInt_normalization f] at hl
  have hr := AdjunctionComplexUniqueness.leftAdjointUniq_homEquiv
    ((OpenForms.imageComplexAdjunctionInt g).comp (OpenForms.imageComplexAdjunctionInt f))
    (OpenForms.imageComplexAdjunctionInt (f ≫ g)) (OpenForms.deRhamSheafPullbackInt (f ≫ g))
  exact hl.trans ((deRhamSheafDirectImageInt_comp f g).trans
    (hr.trans (deRhamSheafPullbackInt_normalization (f ≫ g))).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.PullbackComposition
