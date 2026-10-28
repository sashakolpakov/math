import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalKernelConeFunctor
import OAI.AlgebraicGeometry.ComplexMultiplication.HomologyShiftFunctor

/-! # Canonical Kernel Cone Homology -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalKernelConeHomology

noncomputable section

/-! # Forgetting coefficients preserves the actual canonical relative-cone normalization -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse homology grading map commutes with the coefficient functor. -/
theorem homologyShiftIso_inv_map (K : CochainComplex C ℤ) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n n' : ℤ) (h : 1 + n = n') :
    ((K.sc n').mapHomologyIso F).hom ≫
      F.map (((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso 1 n n' h).inv.app K) =
    (((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso 1 n n' h).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      HomologicalComplex.homologyMap
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).inv.app K) n ≫
        (((K⟦(1 : ℤ)⟧).sc n).mapHomologyIso F).hom := by
  let c := ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso 1 n n' h).app K
  let d := ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso 1 n n' h).app
    ((F.mapHomologicalComplex (.up ℤ)).obj K)
  let a := ((K⟦(1 : ℤ)⟧).sc n).mapHomologyIso F
  let b := (K.sc n').mapHomologyIso F
  let e := HomologicalComplex.homologyMapIso
    (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).app K) n
  have he : a.hom ≫ (F.mapIso c).hom = e.hom ≫ d.hom ≫ b.hom :=
    HomologyShiftFunctor.homologyShiftIso_map K F n n' h
  change b.hom ≫ (F.mapIso c).inv = d.inv ≫ e.inv ≫ a.hom
  rw [Iso.comp_inv_eq, Category.assoc, Category.assoc, he]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse cone identification preserves the actual positive kernel lift. -/
theorem shiftedLiftShortComplex_map_inv (S : ShortComplex (CochainComplex C ℤ))
    (F : C ⥤ D) [F.Additive] :
    Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex
        (S.map (F.mapHomologicalComplex (.up ℤ))) ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso S.g F).inv =
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).inv.app S.X₁ ≫
      (F.mapHomologicalComplex (.up ℤ)).map
        (Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex S) := by
  apply (cancel_mono (CochainComplex.mappingCone.mapHomologicalComplexIso S.g F).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, CanonicalKernelConeFunctor.shiftedLiftShortComplex_map, ← Category.assoc,
    ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
  change Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex
      (S.map (F.mapHomologicalComplex (.up ℤ))) =
    𝟙 _ ≫ Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex
      (S.map (F.mapHomologicalComplex (.up ℤ)))
  rw [Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical short-exact kernel/cone homology map keeps its normalization under coefficients. -/
theorem shortExactHomologyIsoCone_map (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n n' : ℤ) (h : 1 + n = n') :
    ((S.X₁.sc n').mapHomologyIso F).hom ≫
      F.map (Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS n n' h).hom =
    (Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone
      (S.map (F.mapHomologicalComplex (.up ℤ)))
      (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))) n n' h).hom ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.mapHomologicalComplexIso S.g F).inv n ≫
      (((CochainComplex.mappingCone S.g).sc n).mapHomologyIso F).hom := by
  let l := Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex S
  have hn : HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map l) n ≫
      (((CochainComplex.mappingCone S.g).sc n).mapHomologyIso F).hom =
    (((S.X₁⟦(1 : ℤ)⟧).sc n).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap l n) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map l) F
  dsimp only [Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone,
    Iso.trans_hom, Iso.symm_hom, asIso_hom]
  simp only [Iso.app_inv]
  rw [Functor.map_comp, ← Category.assoc, homologyShiftIso_inv_map,
    Category.assoc, Category.assoc, ← hn]
  simp only [Category.assoc]
  change
    (((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso 1 n n' h).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj S.X₁)) ≫
      HomologicalComplex.homologyMap
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).inv.app S.X₁) n ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map l) n ≫
        (((CochainComplex.mappingCone S.g).sc n).mapHomologyIso F).hom =
    (((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso 1 n n' h).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj S.X₁)) ≫
      HomologicalComplex.homologyMap
        (Algebra.Homology.MappingCoconeShortExact.CochainComplex.mappingCocone.shiftedLiftShortComplex
          (S.map (F.mapHomologicalComplex (.up ℤ)))) n ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.mapHomologicalComplexIso S.g F).inv n ≫
        (((CochainComplex.mappingCone S.g).sc n).mapHomologyIso F).hom
  simpa only [l, HomologicalComplex.homologyMap_comp, Category.assoc] using
    congrArg (fun f =>
      (((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso 1 n n' h).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj S.X₁)) ≫
        HomologicalComplex.homologyMap f n ≫
          (((CochainComplex.mappingCone S.g).sc n).mapHomologyIso F).hom)
      (shiftedLiftShortComplex_map_inv S F).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalKernelConeHomology
