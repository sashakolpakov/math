import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Crystalline Base Twist -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist

noncomputable section

/-!
# Twisting the crystalline base by a divided-power automorphism

The underlying thickenings and covering maps are preserved. Composing their
base maps with a divided-power automorphism gives an equivalence with the
site over the correspondingly twisted structure map. This is the base
change needed for semilinear crystalline Frobenius.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f f' : X ⟶ Spec (CommRingCat.of B)}

def twist (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
    (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) :
    IntegralComparison.BigCrystallineSite.Object p B J δ f ⥤ IntegralComparison.BigCrystallineSite.Object p B J δ f' where
  obj U :=
    { ring := U.ring
      base := U.base.comp e.toRingHom
      ideal := U.ideal
      dividedPowers := U.dividedPowers
      baseCompatible := DividedPowers.IsDPMorphism.comp U.dividedPowers U.baseCompatible he
      primeNilpotent := U.primeNilpotent
      nilIdeal := U.nilIdeal
      mapToX := U.mapToX
      overBase := by
        rw [h, ← Category.assoc, U.overBase, Category.assoc, ← Spec.map_comp]
        rfl }
  map {U V} α :=
    { ringMap := α.ringMap
      overBase := congrArg (fun g : B →+* U.ring => g.comp e.toRingHom) α.overBase
      overX := α.overX }
  map_id U := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl
  map_comp α β := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl

theorem twist_cartesian (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
    (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
    {U V : IntegralComparison.BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) :
    IntegralComparison.BigCrystallineSite.Object.Cartesian ((twist e he h).map α) ↔ IntegralComparison.BigCrystallineSite.Object.Cartesian α := Iff.rfl

theorem inverse_structure (e : B ≃+* B)
    (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) :
    f = f' ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom) := by
  rw [h, Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom = 𝟙 _ := by
    ext b
    exact e.apply_symm_apply b
  rw [he, Spec.map_id, Category.comp_id]

def doubleTwistIso (e : B ≃+* B)
    (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
    (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
    (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) (U : IntegralComparison.BigCrystallineSite.Object p B J δ f) :
    U ≅ (twist e.symm he' (inverse_structure e h)).obj ((twist e he h).obj U) where
  hom :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := by
        apply RingHom.ext
        intro b
        exact congrArg U.base (e.apply_symm_apply b)
      overX := by
        change Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ U.mapToX = U.mapToX
        rw [IntegralComparison.BigCrystallineSite.Object.quotientMap_id]
        change Spec.map (𝟙 (CommRingCat.of (U.ring ⧸ U.ideal))) ≫ U.mapToX = U.mapToX
        rw [Spec.map_id, Category.id_comp] }
  inv :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := by
        apply RingHom.ext
        intro b
        exact (congrArg U.base (e.apply_symm_apply b)).symm
      overX := by
        change Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ U.mapToX = U.mapToX
        rw [IntegralComparison.BigCrystallineSite.Object.quotientMap_id]
        change Spec.map (𝟙 (CommRingCat.of (U.ring ⧸ U.ideal))) ≫ U.mapToX = U.mapToX
        rw [Spec.map_id, Category.id_comp] }
  hom_inv_id := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl
  inv_hom_id := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl

def twistEquivalence (e : B ≃+* B)
    (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
    (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
    (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) :
    IntegralComparison.BigCrystallineSite.Object p B J δ f ≌ IntegralComparison.BigCrystallineSite.Object p B J δ f' where
  functor := twist e he h
  inverse := twist e.symm he' (inverse_structure e h)
  unitIso := NatIso.ofComponents (doubleTwistIso e he he' h) (by
    intro U V α
    apply IntegralComparison.BigCrystallineSite.Object.Hom.ext
    rfl)
  counitIso := NatIso.ofComponents
    (fun U => (doubleTwistIso e.symm he' he (inverse_structure e h) U).symm) (by
      intro U V α
      apply IntegralComparison.BigCrystallineSite.Object.Hom.ext
      rfl)
  functor_unitIso_comp U := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl

theorem twist_ambient_presieve (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
    (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
    {U : IntegralComparison.BigCrystallineSite.Object p B J δ f} (R : Presieve U) :
    (R.map (twist e he h)).map IntegralComparison.BigCrystallineSite.Object.ambient = R.map IntegralComparison.BigCrystallineSite.Object.ambient := by
  obtain ⟨ι, V, α, rfl⟩ := R.exists_eq_ofArrows
  simp only [Presieve.map_ofArrows]
  rfl

theorem twist_preserves_coverings (e : B ≃+* B) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
    (h : f' = f ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) :
    IntegralComparison.BigCrystallineSite.Object.precoverage (p := p) (J := J) (δ := δ) (f := f) ≤
      IntegralComparison.BigCrystallineSite.Object.precoverage.comap (twist e he h) := by
  intro U R hR
  refine ⟨?_, ?_⟩
  · rw [twist_ambient_presieve]
    exact hR.1
  · intro V α hα
    cases hα with
    | of hα => exact hR.2 _ hα

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist
