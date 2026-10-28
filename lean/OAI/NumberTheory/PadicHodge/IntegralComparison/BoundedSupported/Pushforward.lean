import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechPushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechGlobal

/-! # Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Pushforward

noncomputable section

/-! The actual support-forgetting map on the pushed bounded resolution
has the original bounded crystalline value, through its literal global
sections and inverse-image principal diagram. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {X : TopCat.{u}} (f : Y.toTopCat ⟶ X)
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Opens X)

abbrev complex := BoundedOpen.FlasqueComplex.complex fY n I
abbrev pushed := Supported.SectionsPushforward.pushed f (complex fY n I)
abbrev pulled := Supported.OrderedCechPushforward.pulled f F

def globalHomologyIso (q : ℕ) :=
  homologyMapIso (Supported.SectionsPushforward.globalIso f (complex fY n I)) q ≪≫
    BoundedOpen.SectionGlobal.homologyIso fY n I q

variable (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q r, ((Supported.OrderedCechEdge.bicomplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) X F U (pushed fY n I f)).X q).ExactAt (r+1))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)

def toBounded (q : ℕ) :=
  Supported.OrderedCech.Comparison.forgetSupport.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) X F U O (pushed fY n I f)
      hO hcover hrows hglobal q ≫ (globalHomologyIso fY n I f q).hom

theorem comparison (q : ℕ) : toBounded fY n I f F U O hO hcover hrows hglobal q =
    homologyMap (Supported.OrderedCechPushforward.totalIso.{u+1,u,u,u+2}
      (Crystalline.ExactRestriction.Coeff (B := B)) f F U (complex fY n I)).hom q ≫
    Cech.toBounded fY n I (pulled f F) U
      ((Supported.SectionsPushforward.preimage f).obj O)
      (Supported.OrderedCechPushforward.pulled_below f F U O hO)
      (Supported.OrderedCechPushforward.pulled_cover f F U O hcover)
      (Supported.OrderedCechPushforward.pulled_rows.{u+1,u,u,u+2}
        (Crystalline.ExactRestriction.Coeff (B := B)) f F U (complex fY n I) hrows)
      (Supported.OrderedCechPushforward.pulled_global f F O hglobal) q := by
  have h := congrArg (fun a => a ≫ (BoundedOpen.SectionGlobal.homologyIso fY n I q).hom)
    (Supported.OrderedCechPushforward.forgetSupport.{u+1,u,u,u+2}
      (Crystalline.ExactRestriction.Coeff (B := B)) f F U O (complex fY n I)
      hO hcover hrows hglobal q)
  simp only [Category.assoc] at h
  rw [← CechGlobal.factorization] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Pushforward
