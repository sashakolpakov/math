import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech

/-! # Cech Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechGlobal

noncomputable section

/-! The bounded supported map is the original support-forgetting map
followed by the original global-section coordinates of the resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Y.Opens) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Y.Opens)
  (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q r, ((Cech.bicomplex fY n I F U).X q).ExactAt (r+1))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)

theorem factorization (q : ℕ) :
    Cech.toBounded fY n I F U O hO hcover hrows hglobal q =
      Supported.OrderedCech.Comparison.forgetSupport.{u+1,u,u,u+2}
        (Crystalline.ExactRestriction.Coeff (B := B)) Y.toTopCat F U O
        (BoundedOpen.FlasqueComplex.complex fY n I) hO hcover hrows hglobal q ≫
      (BoundedOpen.SectionGlobal.homologyIso fY n I q).hom := by
  exact (Category.assoc _ _ _).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechGlobal
