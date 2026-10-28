import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SingleCechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CoverCoefficients

/-! # Resolution Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionCechRefinement

noncomputable section

/-! The chosen resolution inherits the actual affine refinement
isomorphisms through its original augmentation. Integer coefficient
coordinates are reflected through the genuine forgetful equivalence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem square_isIso {D : Type*} [Category D] {A B C E : D}
    (a : A ⟶ B) (b : C ⟶ E) (e : A ⟶ C) (f : B ⟶ E)
    [IsIso a] [IsIso e] [IsIso f] (h : e ≫ b = a ≫ f) : IsIso b := by
  have hb : b = inv e ≫ a ≫ f := by
    apply (cancel_epi e).mp
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using h
  rw [hb]
  infer_instance

private theorem reflect_square {D E : Type*} [Category D] [Category E]
    (G : D ⥤ E) [G.ReflectsIsomorphisms] {A B : D} {C F : E}
    (eA : G.obj A ≅ C) (eB : G.obj B ≅ F)
    (a : A ⟶ B) (b : C ⟶ F) [IsIso b]
    (h : G.map a ≫ eB.hom = eA.hom ≫ b) : IsIso a := by
  have ha : G.map a = eA.hom ≫ b ≫ eB.inv := by
    apply (cancel_mono eB.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
  let : IsIso (G.map a) := by rw [ha]; infer_instance
  exact isIso_of_reflects_iso a G

open OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrderedInjective.Comparison OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates
variable {X : Scheme.{0}} [X.IsSeparated]
  (A : X.Opens) (hA : IsAffineOpen A)
  {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (O : X.Opens)
  (hU : iSup (fun j => A ⊓ U j) = O) (hV : iSup (fun j => A ⊓ V j) = O)
  (haU : ∀ j, IsAffineOpen (U j)) (haV : ∀ j, IsAffineOpen (V j))
  (N : X.Modules) [N.IsQuasicoherent] (c : ℕ)

include hA haU in
theorem relative_augmentation :
    QuasiIso (RelativeCech.Total.sourceMap A U (OrderedInjective.Comparison.augmentation N c)) := by
  change QuasiIso (AugmentedOrdered.CechForgetNaturality.map U
    (((RelativeCech.Refinement.restriction A).mapHomologicalComplex (.up ℕ)).map
      (OrderedInjective.Comparison.augmentation N c)))
  apply Additive.AugmentedCechQuasiIso.quasiIso_of_evaluation
  intro p a
  change QuasiIso (((Acyclic.OpenInjectiveResolution.sections
    (A ⊓ (AugmentedOrdered.Cech.formal U p).obj a)).mapHomologicalComplex (.up ℕ)).map
      (ShiftedOpenInjectiveResolution.augmentation
        (AffinePrincipal.Injective.Comparison.sheaf N) c))
  exact ShiftedOpenInjectiveResolution.sections_quasiIso
    (AffinePrincipal.Injective.Comparison.sheaf N) c _
    (fun q => AffinePrincipal.Injective.Comparison.affine_acyclic N _
      (RelativeCech.CoefficientQuasiIso.intersection_affine A hA U haU p a) q)

include hA O hU hV haU haV in
theorem relative_target (q : ℕ) :
    IsIso (RelativeCech.Refinement.homology A U V r (OrderedInjective.Comparison.targetPresheaf N c) q) := by
  let := SingleCechRefinement.relative A hA U V r O hU hV haU haV N c q
  let := relative_augmentation A hA U haU N c
  let := relative_augmentation A hA V haV N c
  exact square_isIso _ _ _ _
    (RelativeCech.Refinement.homology_naturality A U V r (OrderedInjective.Comparison.augmentation N c) q)

include haU haV in
theorem ordered_target (hUt : iSup U = ⊤) (hVt : iSup V = ⊤) (q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap U V r (OrderedInjective.Comparison.targetPresheaf N c)) q) := by
  let := SingleCechRefinement.ordered U V r haU haV N c hUt hVt q
  let : QuasiIso ((Presheaf.OrderedCover.Comparison.totalFunctor U).map
      (OrderedInjective.Comparison.augmentation N c)) := OrderedInjective.Comparison.quasiIso N c U haU
  let : QuasiIso ((Presheaf.OrderedCover.Comparison.totalFunctor V).map
      (OrderedInjective.Comparison.augmentation N c)) := OrderedInjective.Comparison.quasiIso N c V haV
  exact square_isIso _ _ _ _
    (Presheaf.OrderedCover.Comparison.homology_naturality U V r (OrderedInjective.Comparison.augmentation N c) q)

include hA O hU hV haU haV in
theorem relative_integer (q : ℕ) :
    IsIso (RelativeCech.Refinement.homology A U V r (OrderedInjective.Comparison.integerPresheaf N c) q) := by
  let : IsIso (RelativeCech.Refinement.homology A U V r
      (Principal.CoefficientHomology.mapped Principal.InjectiveIntegerCoordinates.forget (OrderedInjective.Comparison.integerPresheaf N c)) q) :=
    relative_target A hA U V r O hU hV haU haV N c q
  exact reflect_square Principal.InjectiveIntegerCoordinates.forget
    (Principal.CoefficientHomology.relativeIso Principal.InjectiveIntegerCoordinates.forget (OrderedInjective.Comparison.integerPresheaf N c) A U q)
    (Principal.CoefficientHomology.relativeIso Principal.InjectiveIntegerCoordinates.forget (OrderedInjective.Comparison.integerPresheaf N c) A V q)
    _ _ (Principal.CoefficientHomology.refinement Principal.InjectiveIntegerCoordinates.forget (OrderedInjective.Comparison.integerPresheaf N c) A U V r q)

include haU haV in
theorem ordered_integer (hUt : iSup U = ⊤) (hVt : iSup V = ⊤) (q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap U V r (OrderedInjective.Comparison.integerPresheaf N c)) q) := by
  let : IsIso (homologyMap (OrderedCech.Refinement.totalMap U V r
      (Principal.CoefficientHomology.mapped Principal.InjectiveIntegerCoordinates.forget (OrderedInjective.Comparison.integerPresheaf N c))) q) :=
    ordered_target U V r haU haV N c hUt hVt q
  exact reflect_square Principal.InjectiveIntegerCoordinates.forget
    (OrderedCech.CoefficientTotal.homologyIso U Principal.InjectiveIntegerCoordinates.forget (OrderedInjective.Comparison.integerPresheaf N c) q)
    (OrderedCech.CoefficientTotal.homologyIso V Principal.InjectiveIntegerCoordinates.forget (OrderedInjective.Comparison.integerPresheaf N c) q)
    _ _ (Cech.RefinementCoefficientTotal.OrderedCechRefinementCoefficients.homology_natural U V r Principal.InjectiveIntegerCoordinates.forget (OrderedInjective.Comparison.integerPresheaf N c) q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionCechRefinement
