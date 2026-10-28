import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SupportedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientSupported

/-! # Relative Supported Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeSupportedClass

noncomputable section

/-! The original supported localization of a pure sheaf complex is
its actual relative supported lift, with the same surviving sheaf and class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
private theorem reassoc_square {C : Type*} [Category C] {A B D E F G : C}
    (l : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E) (r : E ⟶ F)
    (d : B ⟶ G) (e : G ⟶ E) (h : a ≫ b = d ≫ e) :
    ((l ≫ a) ≫ b) ≫ r = l ≫ (d ≫ (e ≫ r)) := by
  calc
    _ = l ≫ ((a ≫ b) ≫ r) := by simp only [Category.assoc]
    _ = _ := by rw [h]; simp only [Category.assoc]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)

abbrev singleCoefficientIso (S : X.Modules) (c : ℕ) :
    RelativeConcentration.coefficients (SingleAdditiveSections.moduleSingle S c) ≅
      RelativeCech.SupportedCoordinates.underlying AddCommGrpCat.{u} X (SingleAdditiveSections.sheafSingle S c) :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℕ)).mapIso
      ((singleMapHomologicalComplex (SheafOfModules.toSheaf X.ringCatSheaf) (.up ℕ) c).app S)

abbrev relativeSingleIso (S : X.Modules) (c q : ℕ) :=
  homologyMapIso
    (HomologicalComplex₂.total.mapIso
      (((RelativeCech.Total.localFunctor (RelativeConcentration.ambient U hU) (RelativeConcentration.family U hU W)).mapHomologicalComplex
        (.up ℕ)).mapIso (singleCoefficientIso S c)) (.up ℕ)) q

abbrev singleAmbientIso (S : X.Modules) (c q : ℕ) :=
  homologyMapIso (AugmentedCech.AmbientTotal.totalIso (AdditiveSections.opens U hU) W
    (RelativeCech.SupportedCoordinates.underlying AddCommGrpCat.{u} X (SingleAdditiveSections.sheafSingle S c))) q

omit [X.IsSeparated] in
theorem single_comparison (S : X.Modules) (c q : ℕ) :
    (RelativeConcentration.comparison U hU W (SingleAdditiveSections.moduleSingle S c) q).hom ≫ (relativeSingleIso U hU W S c q).hom =
      (SingleAdditiveSections.homologyIso U hU S c W q).hom ≫
        (singleAmbientIso U hU W S c q).hom := by
  have h := congrArg (fun f => homologyMap f q)
    (AugmentedCech.AmbientTotal.naturality (AdditiveSections.opens U hU) W
      (RelativeConcentration.coefficients (SingleAdditiveSections.moduleSingle S c)) (singleCoefficientIso S c).hom)
  rw [homologyMap_comp, homologyMap_comp] at h
  exact (Category.assoc _ _ _).trans
    ((congrArg ((AdditiveSections.homologyIso U hU (SingleAdditiveSections.moduleSingle S c) W q).hom ≫ ·)
      h.symm).trans (Category.assoc _ _ _).symm)

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (f : Z ⟶ X) [IsClosedImmersion f] (N : Z.Modules)
  (e : K.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hW : ∀ i, SectionPresheaf.openSubset U (W i) ≤ SectionIdealPuncturedCover.outside f.ker)

abbrev relativeLift (q : ℕ) :=
  homologyMap (RelativeCech.SupportedRecovery.localLift AddCommGrpCat.{u} X (RelativeConcentration.ambient U hU)
    (RelativeConcentration.family U hU W) (SectionIdealPuncturedCover.outside f.ker)
      (SingleAdditiveSections.sheafSingle (K.homology c) c) (Closed.SupportedSurvivor.terms_zero f N (K.homology c) e c) hW) q

include hW in
theorem localize_relative (q : ℕ) :
    ((PrincipalReference.SupportedClass.Reference.localize U hU W K c hK f N e hW q ≫
      (RelativeConcentration.comparison U hU W K q).hom) ≫ (RelativeConcentration.relativeIso U hU W K c hK q).hom) ≫
        (relativeSingleIso U hU W (K.homology c) c q).hom = relativeLift U hU W K c f N e hW q := by
  have hconc := RelativeConcentration.concentration U hU W K c hK q
  have hsingle := single_comparison U hU W (K.homology c) c q
  have hlift := congrArg (fun a => homologyMap a q)
    (AugmentedCech.AmbientSupported.lift_transport AddCommGrpCat.{u} X (AdditiveSections.opens U hU) W
      (SectionIdealPuncturedCover.outside f.ker) (SingleAdditiveSections.sheafSingle (K.homology c) c)
      (Closed.SupportedSurvivor.terms_zero f N (K.homology c) e c) hW)
  rw [homologyMap_comp] at hlift
  calc
    _ = PrincipalReference.SupportedClass.Reference.localize U hU W K c hK f N e hW q ≫
        (((AdditiveSections.forgetScalars U).mapIso (PrincipalReference.Concentration.Reference.iso U hU W K c hK q)).hom ≫
          ((RelativeConcentration.comparison U hU W (SingleAdditiveSections.moduleSingle (K.homology c) c) q).hom ≫
            (relativeSingleIso U hU W (K.homology c) c q).hom)) := by
      exact reassoc_square _ _ _ _ _ _ hconc.symm
    _ = PrincipalReference.SupportedClass.Reference.localize U hU W K c hK f N e hW q ≫
        ((PrincipalReference.SupportedClass.Reference.concentratedIso U hU W K c hK q).hom ≫
          (singleAmbientIso U hU W (K.homology c) c q).hom) := by
      rw [hsingle]
      rfl
    _ = _ := by
      rw [← Category.assoc, PrincipalReference.SupportedClass.Reference.localize_concentrated]
      exact hlift

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeSupportedClass
