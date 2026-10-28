import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Pushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechPushforwardCoordinates

/-! # Pushforward Identity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.PushforwardIdentity

noncomputable section

/-! Under literal pushforward sections, the total coefficient isomorphism
is the identity, so the supported map directly gives bounded cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Pushforward
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem erase_identity {C : Type*} [Category C] {A B : C}
    (e : A ⟶ A) (g h : A ⟶ B) (he : e = 𝟙 A) (hh : g = e ≫ h) : g = h := by
  simpa only [he, Category.id_comp] using hh

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {X : TopCat.{u}} (f : Y.toTopCat ⟶ X)
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Opens X)

variable (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q r, ((Supported.OrderedCechEdge.bicomplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) X F U (Pushforward.pushed fY n I f)).X q).ExactAt (r+1))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)

abbrev comparison (q : ℕ) :=
  erase_identity _ _ _
    (Supported.OrderedCechPushforwardCoordinates.total_homology.{u+1,u,u,u+2}
      (Crystalline.ExactRestriction.Coeff (B := B)) f F U (Pushforward.complex fY n I) q)
    (Pushforward.comparison fY n I f F U O hO hcover hrows hglobal q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.PushforwardIdentity
