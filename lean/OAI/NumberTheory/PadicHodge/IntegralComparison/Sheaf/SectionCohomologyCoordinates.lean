import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Section Cohomology Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.SectionCohomologyCoordinates

noncomputable section

/-! General coordinate lemmas for the original injective section cohomology comparison. -/

open _root_.CategoryTheory

universe u v z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (R : Type u) [CommRing R] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  [HasExt.{max u z} (Sheaf K (ModuleCat.{u} R))]
  {ZJ : Sheaf J (ModuleCat.{u} R)} {ZK : Sheaf K (ModuleCat.{u} R)}
  (IJ : InjectiveResolution ZJ) (IK : InjectiveResolution ZK)

omit [HasSheafify K (ModuleCat.{u} R)] [HasExt.{max u z} (Sheaf K (ModuleCat.{u} R))] in
theorem homologyIso_hom (i : ℕ) : (PresheafSectionComplex.homologyIso R J IJ i).hom =
    HomologicalComplex.homologyMap (PresheafSectionComplex.complexIso R J IJ.cocomplex).inv i ≫
      (InjectiveSectionCohomology.homologyIso R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) IJ i).hom := rfl

theorem homology
    (a : InjectiveSectionCohomology.complex R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R K) IK ⟶
      InjectiveSectionCohomology.complex R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) IJ)
    (b : PresheafSectionComplex.complex R K IK.cocomplex ⟶
      PresheafSectionComplex.complex R J IJ.cocomplex) (i : ℕ)
    (g : ModuleCat.of R (Abelian.Ext.{max u z} (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R K) ZK i) ⟶
      ModuleCat.of R (Abelian.Ext.{max u z} (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) ZJ i))
    (hc : a ≫ (PresheafSectionComplex.complexIso R J IJ.cocomplex).hom =
      (PresheafSectionComplex.complexIso R K IK.cocomplex).hom ≫ b)
    (he : HomologicalComplex.homologyMap a i ≫
      (InjectiveSectionCohomology.homologyIso R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) IJ i).hom =
        (InjectiveSectionCohomology.homologyIso R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R K) IK i).hom ≫ g) :
    HomologicalComplex.homologyMap b i ≫ (PresheafSectionComplex.homologyIso R J IJ i).hom =
      (PresheafSectionComplex.homologyIso R K IK i).hom ≫ g := by
  have hs := InverseCoordinateHomology.homology
    (PresheafSectionComplex.complexIso R K IK.cocomplex)
    (PresheafSectionComplex.complexIso R J IJ.cocomplex) a b hc i
  let d := (InjectiveSectionCohomology.homologyIso R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) IJ i).hom
  let v := HomologicalComplex.homologyMap (PresheafSectionComplex.complexIso R K IK.cocomplex).inv i
  exact (congrArg (fun f => HomologicalComplex.homologyMap b i ≫ f) (homologyIso_hom R J IJ i)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ d) hs).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => v ≫ f) he).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun f => f ≫ g) (homologyIso_hom R K IK i).symm))))))

omit [HasSheafify K (ModuleCat.{u} R)] [HasExt.{max u z} (Sheaf K (ModuleCat.{u} R))] in
theorem map_to_sections {P M : CochainComplex (ModuleCat.{max u z} R) ℕ}
    (a : P ⟶ M)
    (b : M ⟶ InjectiveSectionCohomology.complex R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) IJ)
    (c : P ⟶ PresheafSectionComplex.complex R J IJ.cocomplex)
    (hc : c = a ≫ b ≫ (PresheafSectionComplex.complexIso R J IJ.cocomplex).hom) (i : ℕ) :
    HomologicalComplex.homologyMap c i ≫ (PresheafSectionComplex.homologyIso R J IJ i).hom =
      HomologicalComplex.homologyMap a i ≫ (HomologicalComplex.homologyMap b i ≫
        (InjectiveSectionCohomology.homologyIso R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) IJ i).hom) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u z} R) (ComplexShape.up ℕ) i
  let e := PresheafSectionComplex.complexIso R J IJ.cocomplex
  let d := (InjectiveSectionCohomology.homologyIso R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) IJ i).hom
  exact (congrArg (fun f => H.map f ≫ (PresheafSectionComplex.homologyIso R J IJ i).hom) hc).trans
    (CoordinateSquare.Comparison.map_postcompose H a b e (H.map b ≫ d) d rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.SectionCohomologyCoordinates
