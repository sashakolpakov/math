import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence

/-! # Scalar Line Gluing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarLineGluing.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: scalar cocycles give actual line-bundle gluing

All gluing maps live in native scheme module categories. The scalar
cocycle is recovered by the canonical trivialization on the cover.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The actual structure-module endomorphism defined by a global scalar. -/
def scalarEnd (X : Scheme.{u}) (r : Γ(X, ⊤)) : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm r

theorem scalarEnd_value (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (scalarEnd X r) = r :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply r

theorem scalarEnd_one (X : Scheme.{u}) : scalarEnd X 1 = 𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm.map_one

theorem scalarEnd_mul (X : Scheme.{u}) (r s : Γ(X, ⊤)) :
    scalarEnd X (r * s) = scalarEnd X r ≫ scalarEnd X s := by
  exact (congrArg (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm (mul_comm r s)).trans
    ((AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm.map_mul s r)

theorem scalarEnd_pullback {X T : Scheme.{u}} (x : T ⟶ X) (r : Γ(X, ⊤)) :
    Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback x (scalarEnd X r) = scalarEnd T (x.appTop r) := by
  apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective T
  rw [Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback_scalar, scalarEnd_value, scalarEnd_value]

/-- A scalar cocycle on all equal-image pairs for a scheme morphism. -/
structure ScalarCocycle {X Y : Scheme.{u}} (f : X ⟶ Y) where
  value {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) : Γ(T, ⊤)
  self {T : Scheme.{u}} (q : T ⟶ Y) (x : T ⟶ X) (hx : x ≫ f = q) : value q x x hx hx = 1
  comp {T : Scheme.{u}} (q : T ⟶ Y) (x y z : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hz : z ≫ f = q) :
    value q x y hx hy * value q y z hy hz = value q x z hx hz
  naturality {T T' : Scheme.{u}} (t : T' ⟶ T) (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    t.appTop (value q x y hx hy) = value (t ≫ q) (t ≫ x) (t ≫ y)
      (by rw [Category.assoc, hx]) (by rw [Category.assoc, hy])

/-- Interpret a scalar as a morphism between the actual two pullbacks
of the trivial line on the covering scheme. -/
def scalarGluing {X T : Scheme.{u}} (x y : T ⟶ X) (r : Γ(T, ⊤)) :
    (Scheme.Modules.pullback x).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⟶
      (Scheme.Modules.pullback y).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x).hom ≫ scalarEnd T r ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso y).inv

theorem scalarGluing_self {X T : Scheme.{u}} (x : T ⟶ X) : scalarGluing x x 1 = 𝟙 _ := by
  rw [scalarGluing, scalarEnd_one, Category.id_comp, Iso.hom_inv_id]

theorem scalarGluing_comp {X T : Scheme.{u}} (x y z : T ⟶ X) (r s : Γ(T, ⊤)) :
    scalarGluing x y r ≫ scalarGluing y z s = scalarGluing x z (r * s) := by
  simp only [scalarGluing, scalarEnd_mul, Category.assoc, Iso.inv_hom_id_assoc]

/-- A functor transports a conjugated map through compatible frame comparisons. -/
theorem transported_conjugation {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B U : C} {A' B' V : D} (a : A ≅ U) (b : B ≅ U) (e : F.obj U ≅ V)
    (cx : F.obj A ≅ A') (cy : F.obj B ≅ B') (a' : A' ≅ V) (b' : B' ≅ V)
    (hx : cx.hom ≫ a'.hom = F.map a.hom ≫ e.hom)
    (hy : cy.hom ≫ b'.hom = F.map b.hom ≫ e.hom) (s : End U) :
    cx.inv ≫ F.map (a.hom ≫ s ≫ b.inv) ≫ cy.hom =
      a'.hom ≫ (e.inv ≫ F.map s ≫ e.hom) ≫ b'.inv := by
  apply (cancel_epi cx.hom).mp
  apply (cancel_mono b'.hom).mp
  simp only [F.map_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hy]
  simp only [← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  rw [hx]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [F.map_comp, Category.assoc]

/-- Pullback of scalar gluing uses the ordinary pullback of the scalar. -/
theorem scalarGluing_pullback {X T T' : Scheme.{u}} (t : T' ⟶ T) (x y : T ⟶ X) (r : Γ(T, ⊤)) :
    (Scheme.Modules.pullbackComp t x).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ≫
      (Scheme.Modules.pullback t).map (scalarGluing x y r) ≫
        (Scheme.Modules.pullbackComp t y).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) =
      scalarGluing (t ≫ x) (t ≫ y) (t.appTop r) := by
  have h := transported_conjugation (Scheme.Modules.pullback t)
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso y) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t)
    ((Scheme.Modules.pullbackComp t x).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))
    ((Scheme.Modules.pullbackComp t y).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (t ≫ x)) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (t ≫ y))
    (Picard.Homomorphisms.UnitPullbackCoherence.Construction.structureModulePullback_comp t x) (Picard.Homomorphisms.UnitPullbackCoherence.Construction.structureModulePullback_comp t y) (scalarEnd T r)
  change _ = (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (t ≫ x)).hom ≫
    Picard.Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback t (scalarEnd T r) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (t ≫ y)).inv at h
  exact h.trans (congrArg (fun a => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (t ≫ x)).hom ≫ a ≫
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (t ≫ y)).inv) (scalarEnd_pullback t r))

/-- Actual native descent data obtained from the scalar cocycle. -/
def ScalarCocycle.nativeDatum {X Y : Scheme.{u}} {f : X ⟶ Y} (D : ScalarCocycle f) :
    Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f where
  module := AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X
  hom q x y hx hy := scalarGluing x y (D.value q x y hx hy)
  hom_self q x hx := by rw [D.self, scalarGluing_self]
  hom_comp q x y z hx hy hz := by rw [scalarGluing_comp, D.comp]
  hom_pullback t q x y hx hy := by rw [scalarGluing_pullback, D.naturality]

theorem pulledModuleFrame_refl {X T : Scheme.{u}} (x : T ⟶ X) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) x = AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x := by
  apply Iso.ext
  change (Scheme.Modules.pullback x).map (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) ≫
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x).hom = (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x).hom
  rw [(Scheme.Modules.pullback x).map_id, Category.id_comp]

theorem scalarGluing_framedEnd {X T : Scheme.{u}} (x y : T ⟶ X) (r : Γ(T, ⊤)) :
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) x).inv ≫ scalarGluing x y r ≫
      (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) y).hom = scalarEnd T r := by
  rw [pulledModuleFrame_refl, pulledModuleFrame_refl]
  simp only [scalarGluing, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The trivial frame of the constructed native datum recovers exactly
the original scalar cocycle. -/
theorem ScalarCocycle.nativeDatum_scalar {X Y T : Scheme.{u}} {f : X ⟶ Y} (D : ScalarCocycle f)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D.nativeDatum (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) q x y hx hy =
      D.value q x y hx hy := by
  exact (congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) (scalarGluing_framedEnd x y (D.value q x y hx hy))).trans
    (scalarEnd_value T (D.value q x y hx hy))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ScalarLineGluing.Construction.LineDescent
