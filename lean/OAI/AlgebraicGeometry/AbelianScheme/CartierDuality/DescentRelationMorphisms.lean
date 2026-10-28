import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineIntrinsicLineDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomBaseChange

/-! # Descent Relation Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DescentRelationMorphisms.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: the actual overlap detects compatibility of descent morphisms
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomBaseChange.Construction

universe u

/-- A commutative square remains commutative under a functor and
the natural comparison isomorphisms at its two endpoints. -/
theorem transport_intertwiner
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (P : D ⥤ E) (F' G' : C ⥤ E)
    (cx : F ⋙ P ≅ F') (cy : G ⋙ P ≅ G')
    {L M : C} (b : L ⟶ M) (a : F.obj L ⟶ G.obj L) (c : F.obj M ⟶ G.obj M)
    (a' : F'.obj L ⟶ G'.obj L) (c' : F'.obj M ⟶ G'.obj M)
    (ha : cx.inv.app L ≫ P.map a ≫ cy.hom.app L = a')
    (hc : cx.inv.app M ≫ P.map c ≫ cy.hom.app M = c')
    (h : F.map b ≫ c = a ≫ G.map b) : F'.map b ≫ c' = a' ≫ G'.map b := by
  have hx : F'.map b ≫ cx.inv.app M = cx.inv.app L ≫ P.map (F.map b) := cx.inv.naturality b
  have hy : P.map (G.map b) ≫ cy.hom.app M = cy.hom.app L ≫ G'.map b := cy.hom.naturality b
  rw [← ha, ← hc, ← Category.assoc, hx]
  simp only [Category.assoc]
  rw [← Category.assoc (P.map (F.map b)) (P.map c) (cy.hom.app M), ← P.map_comp, h, P.map_comp]
  simp only [Category.assoc]
  rw [hy]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (D E : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f) (b : D.module ⟶ E.module)

/-- Compatibility on a single equal-image pair of native test maps. -/
def CompatibleAt {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) : Prop :=
  (Scheme.Modules.pullback x).map b ≫ E.hom q x y hx hy =
    D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map b

/-- Endpoint and base-map equality transport the whole compatibility
proposition, including all dependent pullback module types. -/
theorem compatibleAt_congr {T : Scheme.{u}} (q q' : T ⟶ Y) (x x' y y' : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hx' : x' ≫ f = q') (hy' : y' ≫ f = q')
    (hq : q = q') (hxx : x = x') (hyy : y = y') :
    CompatibleAt D E b q x y hx hy ↔ CompatibleAt D E b q' x' y' hx' hy' := by
  cases hq
  cases hxx
  cases hyy
  rfl

/-- Native compatibility pulls back along an arbitrary test-scheme map. -/
theorem compatibleAt_pullback {T U : Scheme.{u}} (t : U ⟶ T) (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (h : CompatibleAt D E b q x y hx hy) :
    CompatibleAt D E b (t ≫ q) (t ≫ x) (t ≫ y)
      (by rw [Category.assoc, hx]) (by rw [Category.assoc, hy]) :=
  transport_intertwiner (Scheme.Modules.pullback x) (Scheme.Modules.pullback y)
    (Scheme.Modules.pullback t) (Scheme.Modules.pullback (t ≫ x)) (Scheme.Modules.pullback (t ≫ y))
    (Scheme.Modules.pullbackComp t x) (Scheme.Modules.pullbackComp t y)
    b (D.hom q x y hx hy) (E.hom q x y hx hy) _ _
    (D.hom_pullback t q x y hx hy) (E.hom_pullback t q x y hx hy) h

/-- Any actual presentation of the overlap controls compatibility on
every native test scheme. -/
theorem compatible_of_isPullback {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ X) (sq : IsPullback p₁ p₂ f f)
    (q₀ : Z ⟶ Y) (h₁ : p₁ ≫ f = q₀) (h₂ : p₂ ≫ f = q₀)
    (h : CompatibleAt D E b q₀ p₁ p₂ h₁ h₂) {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) : CompatibleAt D E b q x y hx hy := by
  let t : T ⟶ Z := sq.lift x y (hx.trans hy.symm)
  have ht := compatibleAt_pullback D E b t q₀ p₁ p₂ h₁ h₂ h
  have htx : t ≫ p₁ = x := sq.lift_fst _ _ _
  have hty : t ≫ p₂ = y := sq.lift_snd _ _ _
  have htq : t ≫ q₀ = q := by rw [← h₂, ← Category.assoc, hty, hy]
  exact (compatibleAt_congr D E b _ q _ x _ y _ _ hx hy htq htx hty).mp ht

/-- The native scheme-theoretic overlap controls every test scheme,
including all infinitesimal test schemes. -/
theorem compatible_of_overlap
    (h : CompatibleAt D E b (pullback.snd f f ≫ f) (pullback.fst f f) (pullback.snd f f)
      pullback.condition rfl) {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) : CompatibleAt D E b q x y hx hy :=
  compatible_of_isPullback D E b (pullback.fst f f) (pullback.snd f f)
    (IsPullback.of_hasPullback f f) _ pullback.condition rfl h q x y hx hy

/-- A morphism compatible on the actual overlap is a morphism of the
entire ordinary descent data. -/
def nativeDescentHomOfOverlap
    (h : CompatibleAt D E b (pullback.snd f f ≫ f) (pullback.fst f f) (pullback.snd f f)
      pullback.condition rfl) : AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData D ⟶ AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData E :=
  Picard.Homomorphisms.ModuleHomBaseChange.Construction.nativeDescentHom f _ _ b (compatible_of_overlap D E b h)

/-- The standard pullback-composition path is the actual canonical
module descent map on the overlap. -/
theorem canonicalDescent_standard {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X)
    (h : p ≫ f = q ≫ f) (L : Y.Modules) :
    (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L).hom (q ≫ f) p q h rfl =
      (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L := by
  rw [Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom]
  simp only [Picard.PoincareBundle.Cech.MateNormalization.standardGluing, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.trans_refl, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DescentRelationMorphisms.Construction.LineDescent
