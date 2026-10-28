import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTransportedGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinementComponents
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeComponentCongr
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex

/-! # Section Cone Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement

noncomputable section

/-! Cover refinement preserves the original bounded section cone,
with its section and flasque coordinate isomorphisms kept explicit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w s t
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type v} [Category.{w} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (G : C ⥤ D) (F : D ⥤ Y.Opens) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G]
  [∀ (q : ℕ) (t : Fin (q + 1) → κ), PreservesLimit (Discrete.functor (V ∘ t)) F]
  (r : FormalCoproduct.mk ι (G.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.complex fY n I
local notation "M" => Functor.obj (OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.global (TopologicalSpace.Opens Y)) Q

def oldSections := ((IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n ⋙
  NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u + 2} R) F).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
def newSections := ((IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n ⋙
  NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u + 2} R) (G ⋙ F)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex

def sectionIso : oldSections fY n I F ≅
    ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u + 2} R) F).mapHomologicalComplex (.up ℕ)).obj Q := Iso.refl _

def oldCone := FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.cone.{u + 1, u, u + 2} R Y.carrier K F
  (sectionIso fY n I F) (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso fY n I)
def oldEdge := FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.edge.{u + 1, u, u + 2} R Y.carrier K F V
  (sectionIso fY n I F) (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso fY n I)

def oldRawEdge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map V (oldSections fY n I F) M (oldCone fY n I F)

omit [Quiver.IsThin D]
  [∀ (q : ℕ) (t : Fin (q + 1) → κ), PreservesLimit (Discrete.functor (V ∘ t)) F] in
theorem old_edge_component (q : ℕ) : (oldEdge fY n I F V).f q = (oldRawEdge fY n I F V).f q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def newCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ newSections fY n I G F :=
  ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u + 2} R) (G ⋙ F)).mapHomologicalComplex (.up ℕ)).map
    (CechPresheaf.TopCone.CechPresheafTopCone.cone Y.Opens Q)

def newEdge := CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (newSections fY n I G F) M (newCone fY n I G F)

def refinement : (CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V (oldSections fY n I F)).total (.up ℕ) ⟶
    (CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (newSections fY n I G F)).total (.up ℕ) :=
  CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map G U V r (oldSections fY n I F)

def pulledCone : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ newSections fY n I G F :=
  CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone G (oldSections fY n I F) M (oldCone fY n I F)

omit [HasBinaryProducts C] [Quiver.IsThin D] [HasBinaryProducts D] in
theorem cone_component (q : ℕ) (W : Cᵒᵖ) : ((pulledCone fY n I G F).f q).app W =
    ((newCone fY n I G F).f q).app W := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [Quiver.IsThin D] [HasBinaryProducts D]
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G] in
theorem pulled_edge_component (q : ℕ) :
    (CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (newSections fY n I G F) M (pulledCone fY n I G F)).f q =
      (newEdge fY n I G F U).f q :=
  CechPresheaf.ConeComponentCongr.CechPresheafConeComponentCongr.component U _ _ (pulledCone fY n I G F) (newCone fY n I G F) q
    (cone_component fY n I G F q)

omit [∀ (q : ℕ) (t : Fin (q + 1) → κ), PreservesLimit (Discrete.functor (V ∘ t)) F] in
theorem component (q : ℕ) : (oldEdge fY n I F V).f q ≫ (refinement fY n I G F U V r).f q =
    (newEdge fY n I G F U).f q :=
  (congrArg (fun a => a ≫ (refinement fY n I G F U V r).f q) (old_edge_component fY n I F V q)).trans
    ((CechPresheaf.ConeRefinementComponents.CechPresheafConeRefinementComponents.augmentation G U V r (oldSections fY n I F) M
      (oldCone fY n I F) q).trans (pulled_edge_component fY n I G F U q))

omit [∀ (q : ℕ) (t : Fin (q + 1) → κ), PreservesLimit (Discrete.functor (V ∘ t)) F] in
theorem naturality : oldEdge fY n I F V ≫ refinement fY n I G F U V r = newEdge fY n I G F U := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact component fY n I G F U V r q

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement
