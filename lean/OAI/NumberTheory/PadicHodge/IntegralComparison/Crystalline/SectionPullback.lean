import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantSections

/-! # Section Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SectionPullback

noncomputable section

/-! The original crystalline pullback in degree zero is pullback of the actual presheaf section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantSections

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

def sheafSection (s : ConstantSections.Sections (p := p) (J := J) (δ := δ) f) :
    BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f ⟶ BigCrystallineCohomology.structureSheaf f :=
  (presheafToSheaf BigCrystallineSite.Object.topology (ModuleCat.{u + 1} R)).map s

theorem cohomology_mk₀ (s : ConstantSections.Sections (p := p) (J := J) (δ := δ) f) :
    (ConstantSections.cohomologyEquiv f).symm s = Ext.mk₀ (sheafSection f s) := by
  apply (ConstantSections.cohomologyEquiv f).injective
  have h : ConstantSections.cohomologyEquiv f (Ext.mk₀ (sheafSection f s)) = s := by
    change Sheafified.PresheafSections.homLinearEquiv R BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f)
      (StructureDescent.largePresheaf_isSheaf f) (ModuleCat.of R R)
      (Ext.linearEquiv₀ (Ext.mk₀ (sheafSection f s))) = s
    exact (congrArg (Sheafified.PresheafSections.homLinearEquiv R BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f)
      (StructureDescent.largePresheaf_isSheaf f) (ModuleCat.of R R))
        ((Ext.linearEquiv₀ («R» := R)).apply_symm_apply (sheafSection f s))).trans
      (Sheafified.PresheafSections.homLinearEquiv_map R BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f)
        (StructureDescent.largePresheaf_isSheaf f) (ModuleCat.of R R) s)
  exact ((ConstantSections.cohomologyEquiv f).apply_symm_apply s).trans h.symm

variable {f} {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of B)} (g : X ⟶ Y) (hg : g ≫ fY = f)

theorem sheaf_pullback (s : ConstantSections.Sections (p := p) (J := J) (δ := δ) fY) :
    (BigCrystallineCohomology.constantTransport g hg).inv ≫ (ExactRestriction.restriction g hg).map (sheafSection fY s) ≫
      (BigCrystallineCohomology.structureTransport g hg).hom =
        sheafSection f (Functor.whiskerLeft (BigCrystallineSite.postcompose g hg).op s ≫ (BigCrystallineCohomology.presheafTransport g hg).hom) := by
  let e := (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} R) BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology
  let b := (presheafToSheaf BigCrystallineSite.Object.topology (ModuleCat.{u + 1} R)).map
    (Functor.whiskerLeft (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).op s)
  let d := (presheafToSheaf BigCrystallineSite.Object.topology (ModuleCat.{u + 1} R)).map
    (BigCrystallineCohomology.presheafTransport (p := p) (J := J) (δ := δ) g hg).hom
  have h : b ≫ (e.app (BigCrystallineCohomology.largePresheaf fY)).hom =
      (BigCrystallineCohomology.constantTransport g hg).inv ≫ (ExactRestriction.restriction g hg).map
        (sheafSection fY s) := e.hom.naturality s
  change (BigCrystallineCohomology.constantTransport g hg).inv ≫
    (ExactRestriction.restriction g hg).map (sheafSection fY s) ≫
      ((e.app (BigCrystallineCohomology.largePresheaf fY)).inv ≫ d) = _
  have h₁ := congrArg (fun a => a ≫ ((e.app (BigCrystallineCohomology.largePresheaf fY)).inv ≫ d)) h.symm
  have h₂ : (b ≫ (e.app (BigCrystallineCohomology.largePresheaf fY)).hom) ≫ ((e.app (BigCrystallineCohomology.largePresheaf fY)).inv ≫ d) = b ≫ d :=
    (Category.assoc _ _ _).trans
      (congrArg (fun a => b ≫ a) ((e.app (BigCrystallineCohomology.largePresheaf fY)).hom_inv_id_assoc d))
  have h₃ : b ≫ d = sheafSection f
      (Functor.whiskerLeft (BigCrystallineSite.postcompose g hg).op s ≫ (BigCrystallineCohomology.presheafTransport g hg).hom) :=
    ((presheafToSheaf BigCrystallineSite.Object.topology (ModuleCat.{u + 1} R)).map_comp _ _).symm
  exact (Category.assoc _ _ _).symm.trans (h₁.trans (h₂.trans h₃))

theorem cohomology_pullback (s : ConstantSections.Sections (p := p) (J := J) (δ := δ) fY) :
    BigCrystallineCohomology.pullback g hg 0 ((ConstantSections.cohomologyEquiv fY).symm s) =
      (ConstantSections.cohomologyEquiv f).symm
        (Functor.whiskerLeft (BigCrystallineSite.postcompose g hg).op s ≫ (BigCrystallineCohomology.presheafTransport g hg).hom) := by
  rw [cohomology_mk₀, cohomology_mk₀]
  change ((Ext.mk₀ _).comp ((Ext.mk₀ _).mapExactFunctor _) (Nat.zero_add 0)).comp
    (Ext.mk₀ _) (Nat.add_zero 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Category.assoc, sheaf_pullback]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SectionPullback
