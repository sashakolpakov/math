import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechRefinementConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeSupportedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechRefinement

/-! # Supported Pure Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedPureClass

noncomputable section

/-! A globally supported survivor has a canonical class in every affine
relative cover of its pure complex. All refinements carry this class forward. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechRefinementConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))

abbrev sheafCoefficients (S : X.Modules) (c : ℕ) :=
  RelativeCech.SupportedCoordinates.underlying AddCommGrpCat.{u} X (Principal.SingleAdditiveSections.sheafSingle S c)

abbrev singleIso (S : X.Modules) (c q : ℕ) :=
  homologyMapIso (HomologicalComplex₂.total.mapIso
    (((RelativeCech.Total.localFunctor U V).mapHomologicalComplex (.up ℕ)).mapIso
      (Principal.RelativeSupportedClass.singleCoefficientIso S c)) (.up ℕ)) q

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (f : Z ⟶ X) [IsClosedImmersion f] (N : Z.Modules)
  (e : K.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hVO : ∀ i, V i ≤ SectionIdealPuncturedCover.outside f.ker)

abbrev survivorIso (q : ℕ) := AdditiveCechConcentration.iso U hU V hV K c hK q ≪≫ singleIso U V (K.homology c) c q

abbrev sheafLift (q : ℕ) :=
  homologyMap (RelativeCech.SupportedRecovery.localLift AddCommGrpCat.{u} X U V
    (SectionIdealPuncturedCover.outside f.ker) (Principal.SingleAdditiveSections.sheafSingle (K.homology c) c)
      (Closed.SupportedSurvivor.terms_zero f N (K.homology c) e c) hVO) q

def lift (q : ℕ) := sheafLift U V K c f N e hVO q ≫ (survivorIso U hU V hV K c hK q).inv

@[reassoc]
theorem normalization (q : ℕ) : lift U hU V hV K c hK f N e hVO q ≫
    (survivorIso U hU V hV K c hK q).hom = sheafLift U V K c f N e hVO q := by
  dsimp only [lift]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V)
  (hWO : ∀ i, W i ≤ SectionIdealPuncturedCover.outside f.ker)

theorem survivor_refinement (q : ℕ) :
    (survivorIso U hU V hV K c hK q).hom ≫
      RelativeCech.Refinement.homology U V W r (sheafCoefficients (K.homology c) c) q =
    RelativeCech.Refinement.homology U V W r (AdditiveCechConcentration.coefficients K) q ≫
      (survivorIso U hU W hW K c hK q).hom := by
  have hcoeff := RelativeCech.Refinement.homology_naturality U V W r
    (Principal.RelativeSupportedClass.singleCoefficientIso (K.homology c) c).hom q
  have hconc := AdditiveCechRefinementConcentration.refinement_square U hU V hV W hW r K c hK q
  exact (DualComplexHomology.compose_squares _ _ _ _ _ _ _ hconc.symm hcoeff.symm).symm

include hVO hWO in
omit [X.IsSeparated] [∀ (q : ℕ), (K.X q).IsQuasicoherent] in
theorem sheaf_refinement (q : ℕ) : sheafLift U V K c f N e hVO q ≫
    RelativeCech.Refinement.homology U V W r (sheafCoefficients (K.homology c) c) q =
      sheafLift U W K c f N e hWO q := by
  have h := congrArg (fun a => homologyMap a q)
    (Supported.CechRefinement.global_lift AddCommGrpCat.{u} X
      (RelativeCech.Intersections.intersect U) V W r
      (SectionIdealPuncturedCover.outside f.ker) (Principal.SingleAdditiveSections.sheafSingle (K.homology c) c)
      (fun i => inf_le_right.trans (hVO i)) (fun i => inf_le_right.trans (hWO i))
      (Closed.SupportedSurvivor.terms_zero f N (K.homology c) e c))
  rw [homologyMap_comp] at h
  exact h

private theorem lift_refinement {C : Type*} [Category C] {A B D E F : C}
    (e : B ≅ D) (f : E ≅ F) (r : B ⟶ E) (s : D ⟶ F)
    (a : A ⟶ D) (b : A ⟶ F)
    (he : e.hom ≫ s = r ≫ f.hom) (ha : a ≫ s = b) :
    (a ≫ e.inv) ≫ r = b ≫ f.inv := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← he, Iso.inv_hom_id_assoc, ha]

include hVO hWO in
theorem refinement (q : ℕ) : lift U hU V hV K c hK f N e hVO q ≫
    RelativeCech.Refinement.homology U V W r (AdditiveCechConcentration.coefficients K) q =
      lift U hU W hW K c hK f N e hWO q :=
  lift_refinement (survivorIso U hU V hV K c hK q) (survivorIso U hU W hW K c hK q) _ _ _ _
    (survivor_refinement U hU V hV K c hK W hW r q)
    (sheaf_refinement U V K c f N e hVO W r hWO q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedPureClass
