import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCechConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ConcentrationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedPureClass

/-! # Additive Cech Global Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechGlobalConcentration.SupportedPureClass

noncomputable section

/-! The supported pure-complex lift extends to the same original global
Čech class, through the actual concentration maps in its original degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))

abbrev cover := RelativeCech.Intersections.cover U V
abbrev globalFunctor (q : ℕ) := Additive.OrderedCechConcentration.functor (cover U V) q
abbrev extension (K : CochainComplex X.Modules ℕ) (q : ℕ) :=
  homologyMap (RelativeCech.Total.map U V (AdditiveCechConcentration.coefficients K)) q

omit [X.IsSeparated] in
theorem extension_naturality {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) (q : ℕ) :
    (AdditiveCechConcentration.functor U V q).map a ≫ extension U V L q =
      extension U V K q ≫ (globalFunctor U V q).map a :=
  RelativeCech.Total.homology_naturality U V (AdditiveCechConcentration.coefficientMap a) q

abbrev globalSingleIso (S : X.Modules) (c q : ℕ) :=
  homologyMapIso (HomologicalComplex₂.total.mapIso
    (((OrderedCech.Functor.Projection.functor (cover U V)).mapHomologicalComplex (.up ℕ)).mapIso
      (Principal.RelativeSupportedClass.singleCoefficientIso S c)) (.up ℕ)) q

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

abbrev globalIso (q : ℕ) := Additive.OrderedCechConcentration.iso (cover U V)
  (RelativeCech.ConcentrationNaturality.cover_affine U hU V hV) K c hK q

abbrev globalSurvivorIso (q : ℕ) := globalIso U hU V hV K c hK q ≪≫
  globalSingleIso U V (K.homology c) c q

theorem extension_square (q : ℕ) :
    (AdditiveCechConcentration.iso U hU V hV K c hK q).hom ≫
      extension U V ((single X.Modules (.up ℕ) c).obj (K.homology c)) q =
    extension U V K q ≫ (globalIso U hU V hV K c hK q).hom := by
  let := AdditiveCechConcentration.projection_isIso U hU V hV K c hK q
  let := AdditiveCechConcentration.inclusion_isIso U hU V hV K c hK q
  let := Additive.OrderedCechConcentration.projection_isIso (cover U V)
    (RelativeCech.ConcentrationNaturality.cover_affine U hU V hV) K c hK q
  let := Additive.OrderedCechConcentration.inclusion_isIso (cover U V)
    (RelativeCech.ConcentrationNaturality.cover_affine U hU V hV) K c hK q
  exact ConcentrationLocalRecovery.square (AdditiveCechConcentration.functor U V q) (globalFunctor U V q) K c
    (extension U V K q) (extension U V (CohomologyConcentration.truncation K c) q)
    (extension U V ((single X.Modules (.up ℕ) c).obj (K.homology c)) q)
    (extension_naturality U V (CohomologyConcentration.projection K c) q)
    (extension_naturality U V (CohomologyConcentration.inclusion K c) q)

theorem survivor_extension (q : ℕ) :
    (SupportedPureClass.survivorIso U hU V hV K c hK q).hom ≫
      homologyMap (RelativeCech.Total.map U V (SupportedPureClass.sheafCoefficients (K.homology c) c)) q =
    extension U V K q ≫ (globalSurvivorIso U hU V hV K c hK q).hom := by
  have hc := RelativeCech.Total.homology_naturality U V
    (Principal.RelativeSupportedClass.singleCoefficientIso (K.homology c) c).hom q
  exact (DualComplexHomology.compose_squares _ _ _ _ _ _ _
    (extension_square U hU V hV K c hK q).symm hc.symm).symm

variable (f : Z ⟶ X) [IsClosedImmersion f] (N : Z.Modules)
  (e : K.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hVO : ∀ i, V i ≤ SectionIdealPuncturedCover.outside f.ker)

abbrev globalEdge (q : ℕ) := homologyMap
  (Presheaf.OrderedCechEdge.edge (cover U V) (SupportedPureClass.sheafCoefficients (K.homology c) c)) q

private theorem recover {C : Type*} [Category C] {A B D E F : C}
    (e : B ≅ D) (f : E ≅ F) (r : B ⟶ E) (s : D ⟶ F)
    (a : A ⟶ D) (b : A ⟶ F)
    (he : e.hom ≫ s = r ≫ f.hom) (ha : a ≫ s = b) :
    (a ≫ e.inv) ≫ r = b ≫ f.inv := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← he, Iso.inv_hom_id_assoc, ha]

include hVO in
theorem recovery (q : ℕ) : SupportedPureClass.lift U hU V hV K c hK f N e hVO q ≫
    extension U V K q = globalEdge U V K c q ≫ (globalSurvivorIso U hU V hV K c hK q).inv :=
  recover (SupportedPureClass.survivorIso U hU V hV K c hK q) (globalSurvivorIso U hU V hV K c hK q) _ _ _ _
    (survivor_extension U hU V hV K c hK q)
    (RelativeCech.SupportedRecovery.homology_recovery AddCommGrpCat.{u} X U V
      (SectionIdealPuncturedCover.outside f.ker) (Principal.SingleAdditiveSections.sheafSingle (K.homology c) c)
      (Closed.SupportedSurvivor.terms_zero f N (K.homology c) e c) hVO q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechGlobalConcentration.SupportedPureClass
