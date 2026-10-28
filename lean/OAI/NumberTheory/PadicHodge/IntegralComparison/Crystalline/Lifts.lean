import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Coverings

/-! # Lifts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Lifts

noncomputable section

/-!
# IntegralComparison: lifting incoming crystalline morphisms along postcomposition

The lift retains the ambient ring, divided powers, and nilpotence. Its map
to X is the composite of the map on closed subschemes with the given map
to X. The comparison isomorphism retains the ambient ring identically.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {fY : Y ⟶ Spec (CommRingCat.of B)}
variable (g : X ⟶ Y) (hg : g ≫ fY = f)
variable {U : BigCrystallineSite.Object p B J δ f} {V : BigCrystallineSite.Object p B J δ fY}

def liftedObject (α : V ⟶ (BigCrystallineSite.postcompose g hg).obj U) : BigCrystallineSite.Object p B J δ f where
  ring := V.ring
  base := V.base
  ideal := V.ideal
  dividedPowers := V.dividedPowers
  baseCompatible := V.baseCompatible
  primeNilpotent := V.primeNilpotent
  nilIdeal := V.nilIdeal
  mapToX := BigCrystallineSite.Object.closed.map α ≫ U.mapToX
  overBase := by
    let q : Spec (CommRingCat.of (V.ring ⧸ V.ideal)) ⟶
        Spec (CommRingCat.of (U.ring ⧸ U.ideal)) := BigCrystallineSite.Object.closed.map α
    have hα : q ≫ (U.mapToX ≫ g) = V.mapToX := α.overX
    change (q ≫ U.mapToX) ≫ f = _
    calc
      (q ≫ U.mapToX) ≫ f = (q ≫ U.mapToX) ≫ (g ≫ fY) :=
        congrArg (fun t => (q ≫ U.mapToX) ≫ t) hg.symm
      _ = (q ≫ (U.mapToX ≫ g)) ≫ fY := by simp only [Category.assoc]
      _ = V.mapToX ≫ fY := congrArg (fun t => t ≫ fY) hα
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk V.ideal)) ≫
          Spec.map (CommRingCat.ofHom V.base) := V.overBase

def liftedHom (α : V ⟶ (BigCrystallineSite.postcompose g hg).obj U) : liftedObject g hg α ⟶ U where
  ringMap := α.ringMap
  overBase := α.overBase
  overX := rfl

def liftedIso (α : V ⟶ (BigCrystallineSite.postcompose g hg).obj U) :
    (BigCrystallineSite.postcompose g hg).obj (liftedObject g hg α) ≅ V where
  hom :=
    { ringMap := DividedPowers.DPMorphism.id V.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V V (DividedPowers.DPMorphism.id V.dividedPowers))) ≫ V.mapToX =
          (BigCrystallineSite.Object.closed.map α ≫ U.mapToX) ≫ g
        rw [BigCrystallineSite.Object.quotientMap_id]
        simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
        exact α.overX.symm.trans (Category.assoc _ _ _).symm }
  inv :=
    { ringMap := DividedPowers.DPMorphism.id V.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V V (DividedPowers.DPMorphism.id V.dividedPowers))) ≫
          ((BigCrystallineSite.Object.closed.map α ≫ U.mapToX) ≫ g) = V.mapToX
        rw [BigCrystallineSite.Object.quotientMap_id]
        simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
        exact α.overX }
  hom_inv_id := by apply BigCrystallineSite.Object.Hom.ext; rfl
  inv_hom_id := by apply BigCrystallineSite.Object.Hom.ext; rfl

lemma liftedHom_map (α : V ⟶ (BigCrystallineSite.postcompose g hg).obj U) :
    (BigCrystallineSite.postcompose g hg).map (liftedHom g hg α) = (liftedIso g hg α).hom ≫ α := by
  apply BigCrystallineSite.Object.Hom.ext
  rfl

variable {U₁ U₂ U₃ : BigCrystallineSite.Object p B J δ f}

def liftTriangle (a : U₁ ⟶ U₃) (b : U₂ ⟶ U₃)
    (c : (BigCrystallineSite.postcompose g hg).obj U₁ ⟶ (BigCrystallineSite.postcompose g hg).obj U₂)
    (h : c ≫ (BigCrystallineSite.postcompose g hg).map b = (BigCrystallineSite.postcompose g hg).map a) : U₁ ⟶ U₂ where
  ringMap := c.ringMap
  overBase := c.overBase
  overX := by
    let c₀ : DividedPowers.DPMorphism U₂.dividedPowers U₁.dividedPowers := c.ringMap
    have hr : c₀.comp b.ringMap = a.ringMap :=
      congrArg (fun t : (BigCrystallineSite.postcompose g hg).obj U₁ ⟶ (BigCrystallineSite.postcompose g hg).obj U₃ => t.ringMap) h
    let a' := Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U₁ U₃ a.ringMap))
    let b' := Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U₂ U₃ b.ringMap))
    let c' := Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U₁ U₂ c₀))
    have he : c' ≫ b' = a' := by
      dsimp only [a', b', c']
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom
        ((BigCrystallineSite.Object.quotientMap U₁ U₂ c₀).comp (BigCrystallineSite.Object.quotientMap U₂ U₃ b.ringMap))) = _
      rw [← BigCrystallineSite.Object.quotientMap_comp U₁ U₂ U₃ c₀ b.ringMap, hr]
    have hb : b' ≫ U₃.mapToX = U₂.mapToX := b.overX
    have ha : a' ≫ U₃.mapToX = U₁.mapToX := a.overX
    change c' ≫ U₂.mapToX = U₁.mapToX
    rw [← hb, ← Category.assoc, he]
    exact ha

lemma liftTriangle_map (a : U₁ ⟶ U₃) (b : U₂ ⟶ U₃)
    (c : (BigCrystallineSite.postcompose g hg).obj U₁ ⟶ (BigCrystallineSite.postcompose g hg).obj U₂)
    (h : c ≫ (BigCrystallineSite.postcompose g hg).map b = (BigCrystallineSite.postcompose g hg).map a) :
    (BigCrystallineSite.postcompose g hg).map (liftTriangle g hg a b c h) = c := by
  apply BigCrystallineSite.Object.Hom.ext
  rfl

lemma liftTriangle_comp (a : U₁ ⟶ U₃) (b : U₂ ⟶ U₃)
    (c : (BigCrystallineSite.postcompose g hg).obj U₁ ⟶ (BigCrystallineSite.postcompose g hg).obj U₂)
    (h : c ≫ (BigCrystallineSite.postcompose g hg).map b = (BigCrystallineSite.postcompose g hg).map a) :
    liftTriangle g hg a b c h ≫ b = a := by
  apply (BigCrystallineSite.postcompose g hg).map_injective
  rw [Functor.map_comp, liftTriangle_map]
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Lifts
