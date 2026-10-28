import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleReferenceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleModuleCoordinates

/-! # Reference Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ReferenceCoordinates.Reference

noncomputable section

/-! The actual nested-pushforward principal module coordinates agree
with the source-open single-sheaf coordinates in their original degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem change_coordinate {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E : C} {X : D} (a : X ⟶ F.obj A) (e : A ≅ B) (d : A ≅ E) :
    (a ≫ F.map e.hom) ≫ F.map (e.inv ≫ d.hom) = a ≫ F.map d.hom := by
  rw [F.map_comp, Category.assoc a, ← Category.assoc (F.map e.hom),
    ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]

open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
variable {Y X Z : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) {ι : Type} [LinearOrder ι]
  (W : ι → Principal.SectionPresheaf.Index U) (N : Y.Modules) (c g : ℕ)

abbrev original := OpenFixedClass.source f i U hU N
abbrev forgetScalars : ModuleCat.{0} Γ(Z,U) ⥤ AddCommGrpCat := forget₂ _ _

def additiveIso : (Principal.AdditiveSections.additiveFunctor U hU).obj (OpenRestriction.image f i N) ≅
    (OpenReindex.wideOpens (f ≫ i) U hU).op ⋙ (AffinePrincipal.Injective.Comparison.sheaf N).obj :=
  ((Principal.AdditiveSections.functorIso U hU).app (OpenRestriction.image f i N)).symm ≪≫
    OpenScalar.diagramIso f i U hU N

def sourceCoordinates (q : ℕ) (hq : q=g+c) :=
  eqToIso (congrArg (fun k => (AffinePrincipal.Injective.Comparison.source
    (OpenReindex.wideOpens (f ≫ i) U hU) W N c).homology k) hq) ≪≫
    Supported.SingleReferenceCoordinates.Reference.sourceCoordinates W c g (OpenReindex.wideOpens (f ≫ i) U hU) N

theorem coefficient_coordinates :
    (Principal.SingleModuleCoordinates.coefficientIso U hU (OpenRestriction.image f i N) W g).hom ≫
      homologyMap ((AugmentedOrdered.CechFunctor.functor W).map (additiveIso f i U hU N).hom) g =
    (Supported.SingleReferenceCoordinates.Reference.coefficientIso W Γ(Z,U) (original f i U hU N) g).hom ≫
      homologyMap ((AugmentedOrdered.CechFunctor.functor W).map
        (OpenScalar.diagramIso f i U hU N).hom) g := by
  exact change_coordinate
    (AugmentedOrdered.CechFunctor.functor W ⋙ HomologicalComplex.homologyFunctor _ (.up ℕ) g)
    (Supported.SingleReferenceCoordinates.Reference.coefficientIso W Γ(Z,U) (original f i U hU N) g).hom
    ((Principal.AdditiveSections.functorIso U hU).app (OpenRestriction.image f i N))
    (OpenScalar.diagramIso f i U hU N)

theorem wide_coordinates (q : ℕ) (hq : q=g+c) :
    (SupportedCoordinates.wideIso f i U hU W N c q).hom ≫
      (sourceCoordinates f i U hU W N c g q hq).hom =
    (forgetScalars U).map (Principal.SingleModuleCoordinates.moduleCoordinates U hU
      (OpenRestriction.image f i N) c W g q hq).hom ≫
      (Principal.SingleModuleCoordinates.coefficientIso U hU (OpenRestriction.image f i N) W g).hom ≫
      homologyMap ((AugmentedOrdered.CechFunctor.functor W).map (additiveIso f i U hU N).hom) g := by
  subst q
  rw [coefficient_coordinates]
  have h := Supported.SingleReferenceCoordinates.Reference.coordinates W Γ(Z,U) (original f i U hU N) c g
    (OpenReindex.wideOpens (f ≫ i) U hU) N (OpenScalar.diagramIso f i U hU N)
  simp only [SupportedCoordinates.wideIso, sourceCoordinates,
    Principal.SingleModuleCoordinates.moduleCoordinates, eqToIso_refl, Iso.refl_trans]
  convert h using 1 <;> rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ReferenceCoordinates.Reference
