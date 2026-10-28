import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.FrameTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionedIncomingCoordinates

/-! # Incoming Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingMap

noncomputable section

/-! An incoming-site comparison expressed on the original global
section presheaf, with its exact changes of open and indexing family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem complexNatTrans_ext {C D : Type*} [Category C] [Category D]
    [CategoryTheory.Limits.HasZeroMorphisms D]
    {K L : CochainComplex (C ⥤ D) ℕ} (f g : K ⟶ L)
    (h : ∀ q X, (f.f q).app X = (g.f q).app X) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext X
  exact h q X

universe u v v'
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (V : Y.Opens) {D : Type v} [Preorder D] (F : D →o Y.Opens)
  (hF : ∀ d, F d ≤ V)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) f V.ι n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n F
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.localSections (p := p) (J := J) (δ := δ) f n V F
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.iso (p := p) (J := J) (δ := δ) f n V F hF

variable (K L : CochainComplex
  (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) ℕ)
  (b : ((Subsite.restriction (p := p) (J := J) (δ := δ) f V.ι n).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((Subsite.restriction (p := p) (J := J) (δ := δ) f V.ι n).mapHomologicalComplex (.up ℕ)).obj L)

def map : ((S).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj L :=
  SectionedIncomingHomotopy.map R S T e b

theorem map_component (q : ℕ) (d : Dᵒᵖ) :
    ((IncomingMap.map f n V F hF K L b).f q).app d =
      ((e).hom.app (K.X q)).app d ≫ ((T).map (b.f q)).app d ≫
        ((e).inv.app (L.X q)).app d :=
  SectionedIncomingCoordinates.component R S T e b q d

variable {D' : Type v'} [Preorder D'] (r : D' ⥤ D)

def reindexedOpens : D' →o Y.Opens where
  toFun d := F (r.obj d)
  monotone' _ _ h := F.monotone (leOfHom (r.map (homOfLE h)))

theorem hom_reindex (M : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n)
    (d : D'ᵒᵖ) :
    ((SectionSubsite.iso f n V (reindexedOpens F r)
      (fun d => hF (r.obj d))).hom.app M).app d =
        ((SectionSubsite.iso f n V F hF).hom.app M).app (r.op.obj d) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  apply NatTrans.ext
  funext Z
  rfl

theorem inv_reindex (M : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n)
    (d : D'ᵒᵖ) :
    ((SectionSubsite.iso f n V (reindexedOpens F r)
      (fun d => hF (r.obj d))).inv.app M).app d =
        ((SectionSubsite.iso f n V F hF).inv.app M).app (r.op.obj d) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  apply NatTrans.ext
  funext Z
  rfl

theorem local_map_reindex
    {M N : Subsite.ModuleSheaf (p := p) (J := J) (δ := δ) f V.ι n}
    (a : M ⟶ N) (d : D'ᵒᵖ) :
    ((SectionSubsite.localSections f n V (reindexedOpens F r)).map a).app d =
      ((SectionSubsite.localSections f n V F).map a).app (r.op.obj d) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem reindex_component (q : ℕ) (d : D'ᵒᵖ) :
    ((IncomingMap.map f n V (reindexedOpens F r) (fun d => hF (r.obj d)) K L b).f q).app d =
      ((IncomingMap.map f n V F hF K L b).f q).app (r.op.obj d) := by
  rw [map_component, map_component]
  rw [hom_reindex, local_map_reindex, inv_reindex]

/-- The incoming map after whiskering the indexing family. -/
def whiskeredMap :
    ((SectionSubsite.globalSections f n (reindexedOpens F r)).mapHomologicalComplex (.up ℕ)).obj K ⟶
    ((SectionSubsite.globalSections f n (reindexedOpens F r)).mapHomologicalComplex (.up ℕ)).obj L :=
  (((Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ
      (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)))).obj r.op).mapHomologicalComplex (.up ℕ)).map
        (IncomingMap.map f n V F hF K L b)

private theorem reindex_degree (q : ℕ) :
    (IncomingMap.map f n V (reindexedOpens F r) (fun d => hF (r.obj d)) K L b).f q =
    (whiskeredMap f n V F hF K L b r).f q := by
  apply NatTrans.ext
  funext d
  exact reindex_component f n V F hF K L b r q d

theorem reindex : IncomingMap.map f n V (reindexedOpens F r) (fun d => hF (r.obj d)) K L b =
    whiskeredMap f n V F hF K L b r := by
  exact HomologicalComplex.hom_ext _ _ (reindex_degree f n V F hF K L b r)

variable (V' : Y.Opens) (hV : V = V')

def transport
    (b' : ((Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj L) :
    ((R).mapHomologicalComplex (.up ℕ)).obj K ⟶ ((R).mapHomologicalComplex (.up ℕ)).obj L := by
  subst V'
  exact b'

theorem open_eq (hF' : ∀ d, F d ≤ V')
    (b' : ((Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj L) :
    IncomingMap.map f n V F hF K L (transport f n V K L V' hV b') = IncomingMap.map f n V' F hF' K L b' := by
  subst V'
  rfl

variable (F' : D →o Y.Opens) (h : F = F')

def familyIso : SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n F ≅
    SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n F' :=
  eqToIso (congrArg (SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n) h)

theorem family_eq (hF' : ∀ d, F' d ≤ V) :
    IncomingMap.map f n V F hF K L b ≫ ((NatIso.mapHomologicalComplex (familyIso f n F F' h) (.up ℕ)).app L).hom =
      ((NatIso.mapHomologicalComplex (familyIso f n F F' h) (.up ℕ)).app K).hom ≫
        IncomingMap.map f n V F' hF' K L b := by
  subst F'
  change IncomingMap.map f n V F hF K L b ≫ 𝟙 _ = 𝟙 _ ≫ IncomingMap.map f n V F hF' K L b
  rw [Category.comp_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingMap
