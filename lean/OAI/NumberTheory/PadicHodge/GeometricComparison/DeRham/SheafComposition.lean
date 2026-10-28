import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ImageComposition

/-! # Sheaf Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafComposition

noncomputable section

/-! Composition of native differential-form and sheaf-complex pullbacks over an arbitrary base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R : Type} [CommRing R]
  {X Y Z : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem sectionPullback_comp (U : Z.left.Opens) :
    (Int.sectionPullback f (g.left ⁻¹ᵁ U)).comp (Int.sectionPullback g U) = Int.sectionPullback (f ≫ g) U := by
  ext a
  rfl

theorem formsPullback_comp (n : ℕ) :
    Int.formsPullback g n ≫ (Int.directImagePresheaf g).map (Int.formsPullback f n) = Int.formsPullback (f ≫ g) n := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  have he : CommAlgCat.ofHom (Int.sectionPullback g U.unop) ≫
      CommAlgCat.ofHom (Int.sectionPullback f (g.left ⁻¹ᵁ U.unop)) =
        CommAlgCat.ofHom (Int.sectionPullback (f ≫ g) U.unop) := by
    apply CommAlgCat.hom_ext
    exact sectionPullback_comp f g U.unop
  exact (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp (CommAlgCat.ofHom (Int.sectionPullback g U.unop))
    (CommAlgCat.ofHom (Int.sectionPullback f (g.left ⁻¹ᵁ U.unop))) n ω).symm.trans
      (congrArg (fun a => AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap a n ω) he)

theorem presheafPullback_comp : Int.presheafPullback g ≫
    ((Int.directImagePresheaf g).mapHomologicalComplex (ComplexShape.up ℕ)).map (Int.presheafPullback f) =
      Int.presheafPullback (f ≫ g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact formsPullback_comp f g n

theorem sheafDirectImage_unit {T V : Over (Spec (CommRingCat.of R))} (k : T ⟶ V) :
    (Int.sheafificationComplexAdjunction V).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R V) ≫
        ((sheafToPresheaf (Opens.grothendieckTopology V.left) (ModuleCat.{0} R)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (Int.sheafDirectImage k) =
      Int.presheafToDirectImageSheafComplex k := by
  have h := ((Int.sheafificationComplexAdjunction V).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R V)
    (((Int.directImage k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R T))).apply_symm_apply (Int.presheafToDirectImageSheafComplex k)
  exact h

theorem sheafDirectImage_comp :
    Int.sheafDirectImage g ≫
        ((Int.directImage g).mapHomologicalComplex (ComplexShape.up ℕ)).map (Int.sheafDirectImage f) =
      Int.sheafDirectImage (f ≫ g) := by
  let UZ := (sheafToPresheaf (Opens.grothendieckTopology Z.left) (ModuleCat.{0} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let UY := (sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let Dg := (Int.directImagePresheaf g).mapHomologicalComplex (ComplexShape.up ℕ)
  let Df := (Int.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)
  let Gg := (Int.directImage g).mapHomologicalComplex (ComplexShape.up ℕ)
  let ηX := (Int.sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
  let ηY := (Int.sheafificationComplexAdjunction Y).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y)
  let ηZ := (Int.sheafificationComplexAdjunction Z).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Z)
  let pg := Int.presheafPullback g
  let pf := Int.presheafPullback f
  let pfg := Int.presheafPullback (f ≫ g)
  let dg := Int.sheafDirectImage g
  let df := Int.sheafDirectImage f
  let dfg := Int.sheafDirectImage (f ≫ g)
  have hg : ηZ ≫ UZ.map dg = pg ≫ Dg.map ηY := sheafDirectImage_unit g
  have hf : ηY ≫ UY.map df = pf ≫ Df.map ηX := sheafDirectImage_unit f
  have hfg : ηZ ≫ UZ.map dfg = pfg ≫ Dg.map (Df.map ηX) := sheafDirectImage_unit (f ≫ g)
  have hp : pg ≫ Dg.map pf = pfg := presheafPullback_comp f g
  apply ((Int.sheafificationComplexAdjunction Z).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Z)
    (((Int.directImage (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))).injective
  change ηZ ≫ UZ.map (dg ≫ Gg.map df) = ηZ ≫ UZ.map dfg
  erw [UZ.map_comp dg (Gg.map df), ← Category.assoc, hg, hfg]
  change (pg ≫ Dg.map ηY) ≫ Dg.map (UY.map df) = pfg ≫ Dg.map (Df.map ηX)
  erw [Category.assoc, ← Dg.map_comp, hf, Dg.map_comp, ← Category.assoc, hp]
  rfl

theorem sheafPullback_normalization {T V : Over (Spec (CommRingCat.of R))} (k : T ⟶ V) :
    (Int.imageComplexAdjunction k).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R V)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R T) (Int.sheafPullback k) = Int.sheafDirectImage k :=
  ((Int.imageComplexAdjunction k).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R V)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R T)).apply_symm_apply (Int.sheafDirectImage k)

theorem sheafPullback_comp :
    ((Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map (Int.sheafPullback g) ≫
        Int.sheafPullback f =
      (ImageComposition.inverseImageComplexCompIso f g).hom.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Z) ≫
        Int.sheafPullback (f ≫ g) := by
  apply (((Int.imageComplexAdjunction g).comp (Int.imageComplexAdjunction f)).homEquiv
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Z) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).injective
  have hl := AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.comp_homEquiv_map_comp (Int.imageComplexAdjunction g)
    (Int.imageComplexAdjunction f) (Int.sheafPullback g) (Int.sheafPullback f)
  erw [sheafPullback_normalization g, sheafPullback_normalization f] at hl
  have hr := AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.leftAdjointUniq_homEquiv
    ((Int.imageComplexAdjunction g).comp (Int.imageComplexAdjunction f))
    (Int.imageComplexAdjunction (f ≫ g)) (Int.sheafPullback (f ≫ g))
  exact hl.trans ((sheafDirectImage_comp f g).trans
    (hr.trans (sheafPullback_normalization (f ≫ g))).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafComposition
