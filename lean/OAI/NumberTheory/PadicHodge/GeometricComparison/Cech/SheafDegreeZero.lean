import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermsAreSheaves
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationLeft
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Resolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections

/-! # Sheaf Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.SheafDegreeZero.CechSheafDegreeZero

noncomputable section

/-! The actual native Čech augmentation of any module sheaf is left exact on every open; for a cover it identifies sections with zero-cocycles. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
  {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)

include hU in
theorem presheaf_leftExact :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.presheafInitial R X U F.obj).Exact ∧
      Mono (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.presheafInitial R X U F.obj).f := by
  let G := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafification R X
  let a := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafAugmentation R X U F.obj
  have ha : QuasiIso a := AlgebraicGeometry.Crystalline.Cohomology.Cech.Resolution.CechResolution.augmentation_quasiIso R X U F.obj hU
  have hK : (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X)).obj F.obj))).d 0 1 = 0 :=
    (congrArg G.map (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 F.obj 0 1)).trans
      (G.map_zero _ _)
  have hE : ((AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.presheafInitial R X U F.obj).map G).Exact ∧
      Mono ((AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.presheafInitial R X U F.obj).map G).f :=
    (AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion.quasiIsoAt_zero_iff a hK).mp (ha.quasiIsoAt 0)
  have : Mono ((AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.presheafInitial R X U F.obj).map
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))).f := hE.2
  exact SheafificationLeft.SheafificationLeftExactness.of_sheafification (Opens.grothendieckTopology X)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.presheafInitial R X U F.obj) F.property
    (TermsAreSheaves.CechTermsAreSheaves.isSheaf R X F U 0) (TermsAreSheaves.CechTermsAreSheaves.isSheaf R X F U 1) hE.1

include hU in
theorem sections_leftExact (V : X.Opens) :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.initial R X U F.obj V).Exact ∧
      Mono (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.initial R X U F.obj V).f := by
  have hE := presheaf_leftExact R X F U hU
  have := hE.2
  refine ⟨hE.1.map ((CategoryTheory.evaluation _ _).obj (op V)), ?_⟩
  change Mono (((CategoryTheory.evaluation _ _).obj (op V)).map
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.presheafInitial R X U F.obj).f)
  infer_instance

include hU in
theorem augmentation_quasiIsoAt_zero (V : X.Opens) :
    QuasiIsoAt (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.augmentation R X U F.obj V) 0 :=
  (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.quasiIsoAt_zero_iff R X U F.obj V).mpr
    (sections_leftExact R X F U hU V)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.SheafDegreeZero.CechSheafDegreeZero
