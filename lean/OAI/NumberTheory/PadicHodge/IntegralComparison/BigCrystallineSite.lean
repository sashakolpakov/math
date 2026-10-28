import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

/-! # Big Crystalline Site -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

noncomputable section

/-!
# IntegralComparison: the affine presentation of the big crystalline site

The closed subscheme of a thickening may map arbitrarily to X. Covering
maps must be cartesian on the closed subschemes as well as Zariski covers
on the ambient schemes. These are the covering conditions in Stacks,
Definition 60.8.4: https://stacks.math.columbia.edu/tag/07IB.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (B : Type u) [CommRing B] (J : Ideal B) (δ : DividedPowers J)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

structure Object where
  ring : CommRingCat.{u}
  base : B →+* ring
  ideal : Ideal ring
  dividedPowers : DividedPowers ideal
  baseCompatible : DividedPowers.IsDPMorphism δ dividedPowers base
  primeNilpotent : IsNilpotent (p : ring)
  nilIdeal : ∀ x ∈ ideal, IsNilpotent x
  mapToX : Spec (CommRingCat.of (ring ⧸ ideal)) ⟶ X
  overBase : mapToX ≫ f =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ideal)) ≫ Spec.map (CommRingCat.ofHom base)

variable {p B J δ f}

namespace Object

variable (U V W : Object p B J δ f)

def quotientMap (φ : DividedPowers.DPMorphism V.dividedPowers U.dividedPowers) :
    V.ring ⧸ V.ideal →+* U.ring ⧸ U.ideal :=
  Ideal.quotientMap U.ideal φ.toRingHom (Ideal.map_le_iff_le_comap.mp φ.ideal_comp)

lemma quotientMap_id : Object.quotientMap U U (DividedPowers.DPMorphism.id U.dividedPowers) =
    RingHom.id (U.ring ⧸ U.ideal) := by ext x; rfl

lemma quotientMap_comp
    (φ : DividedPowers.DPMorphism V.dividedPowers U.dividedPowers)
    (ψ : DividedPowers.DPMorphism W.dividedPowers V.dividedPowers) :
    Object.quotientMap U W (φ.comp ψ) = (Object.quotientMap U V φ).comp (Object.quotientMap V W ψ) := by ext x; rfl

structure Hom where
  ringMap : DividedPowers.DPMorphism V.dividedPowers U.dividedPowers
  overBase : ringMap.toRingHom.comp V.base = U.base
  overX : Spec.map (CommRingCat.ofHom (Object.quotientMap U V ringMap)) ≫ V.mapToX = U.mapToX

@[ext]
lemma Hom.ext {α β : Object.Hom U V} (h : α.ringMap = β.ringMap) : α = β := by
  cases α
  cases β
  cases h
  rfl

def id : Object.Hom U U where
  ringMap := DividedPowers.DPMorphism.id U.dividedPowers
  overBase := rfl
  overX := by rw [quotientMap_id]; simp

def comp (α : Object.Hom U V) (β : Object.Hom V W) : Object.Hom U W where
  ringMap := α.ringMap.comp β.ringMap
  overBase := by
    change α.ringMap.toRingHom.comp (β.ringMap.toRingHom.comp W.base) = U.base
    rw [β.overBase, α.overBase]
  overX := by
    rw [quotientMap_comp]
    change Spec.map (CommRingCat.ofHom (Object.quotientMap V W β.ringMap) ≫
      CommRingCat.ofHom (Object.quotientMap U V α.ringMap)) ≫ W.mapToX = _
    rw [Spec.map_comp, Category.assoc, β.overX, α.overX]

instance : Category (Object p B J δ f) where
  Hom := Object.Hom
  id := fun U => Object.id U
  comp := fun {U V W} α β => Object.comp U V W α β
  id_comp α := by apply Object.Hom.ext; rfl
  comp_id α := by apply Object.Hom.ext; rfl
  assoc α β γ := by apply Object.Hom.ext; rfl

def ambient : Object p B J δ f ⥤ Scheme.{u} where
  obj U := Spec U.ring
  map α := Spec.map (CommRingCat.ofHom α.ringMap.toRingHom)
  map_id U := by change Spec.map (𝟙 U.ring) = _; simp
  map_comp α β := by
    change Spec.map (CommRingCat.ofHom β.ringMap.toRingHom ≫
      CommRingCat.ofHom α.ringMap.toRingHom) = _
    exact Spec.map_comp _ _

def closed : Object p B J δ f ⥤ Scheme.{u} where
  obj U := Spec (CommRingCat.of (U.ring ⧸ U.ideal))
  map {U V} α := Spec.map (CommRingCat.ofHom (Object.quotientMap U V α.ringMap))
  map_id U := by
    change Spec.map (CommRingCat.ofHom (Object.quotientMap U U (DividedPowers.DPMorphism.id U.dividedPowers))) = _
    rw [quotientMap_id]
    simp
  map_comp {U V W} α β := by
    change Spec.map (CommRingCat.ofHom (Object.quotientMap U W (α.ringMap.comp β.ringMap))) = _
    rw [quotientMap_comp]
    change Spec.map (CommRingCat.ofHom (Object.quotientMap V W β.ringMap) ≫
      CommRingCat.ofHom (Object.quotientMap U V α.ringMap)) = _
    exact Spec.map_comp _ _

def closedImmersion : closed (p := p) (B := B) (J := J) (δ := δ) (f := f) ⟶ ambient where
  app U := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk U.ideal))
  naturality {U V} α := by
    change Spec.map (CommRingCat.ofHom (Object.quotientMap U V α.ringMap)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk V.ideal)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk U.ideal)) ≫
        Spec.map (CommRingCat.ofHom α.ringMap.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

/-- The closed subscheme is pulled back along a crystalline covering map. -/
def Cartesian {U V : Object p B J δ f} (α : U ⟶ V) : Prop :=
  IsPullback (closed.map α) (closedImmersion.app U) (closedImmersion.app V) (ambient.map α)

def precoverage : Precoverage (Object p B J δ f) where
  coverings U := {R | R.map ambient ∈ Scheme.precoverage IsOpenImmersion (ambient.obj U) ∧
    ∀ ⦃V⦄ (α : V ⟶ U), R α → Cartesian α}

def topology : GrothendieckTopology (Object p B J δ f) := Object.precoverage.toGrothendieck

end Object

/-- The existing small crystalline site includes into the big one. -/
def fromSmall : Crystalline.Site.AffineThickening p B J δ f ⥤ Object p B J δ f where
  obj U :=
    { ring := U.ring
      base := U.base
      ideal := U.ideal
      dividedPowers := U.dividedPowers
      baseCompatible := U.baseCompatible
      primeNilpotent := U.primeNilpotent
      nilIdeal := U.nilIdeal
      mapToX := U.openMap
      overBase := U.overBase }
  map α := { ringMap := α.ringMap, overBase := α.overBase, overX := α.overX }
  map_id U := by apply Object.Hom.ext; rfl
  map_comp α β := by apply Object.Hom.ext; rfl

variable {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of B)}

/-- Composition on X gives the underlying functor needed for crystalline
pullback; ambient rings and divided powers are preserved. -/
def postcompose (g : X ⟶ Y) (hg : g ≫ fY = f) : Object p B J δ f ⥤ Object p B J δ fY where
  obj U :=
    { ring := U.ring
      base := U.base
      ideal := U.ideal
      dividedPowers := U.dividedPowers
      baseCompatible := U.baseCompatible
      primeNilpotent := U.primeNilpotent
      nilIdeal := U.nilIdeal
      mapToX := U.mapToX ≫ g
      overBase := by rw [Category.assoc, hg]; exact U.overBase }
  map {U V} α :=
    { ringMap := α.ringMap
      overBase := α.overBase
      overX := by
        change Spec.map (CommRingCat.ofHom (Object.quotientMap U V α.ringMap)) ≫
          (V.mapToX ≫ g) = U.mapToX ≫ g
        exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ g) α.overX) }
  map_id U := by apply Object.Hom.ext; rfl
  map_comp α β := by apply Object.Hom.ext; rfl

lemma postcompose_cartesian (g : X ⟶ Y) (hg : g ≫ fY = f)
    {U V : Object p B J δ f} (α : U ⟶ V) :
    Object.Cartesian ((postcompose g hg).map α) ↔ Object.Cartesian α := Iff.rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
