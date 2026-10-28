import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow

/-! # Small Crystalline Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineEquivalence.SmallCrystallineAdapter

noncomputable section

/-! Equivalence of the two concrete affine crystalline categories. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
  {X : Over (Spec (CommRingCat.of k))}

theorem residueBase65_to65 (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) :
    SmallCrystallineDpow.SmallCrystallineAdapter.residueBase65 (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S) =
      (SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv S).symm.toRingHom.comp (algebraMap k S.residueRing) := by
  have h := SmallCrystallineDpow.SmallCrystallineAdapter.residueBase65_spec (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S)
  change Spec.map (CommRingCat.ofHom (SmallCrystallineDpow.SmallCrystallineAdapter.residueBase65 (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S))) =
    ((SmallCrystallineDpow.SmallCrystallineAdapter.residueSchemeIso S).hom ≫ S.immersion) ≫ X.hom at h
  rw [Category.assoc, S.over_base, SmallCrystallineDpow.SmallCrystallineAdapter.residueSchemeIso_hom, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

def unitReduced (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) :
    (SmallCrystallineDpow.SmallCrystallineAdapter.to62Object (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S)).residueRing →ₐ[k] S.residueRing where
  __ := (SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv S).toRingHom
  commutes' c := by
    change SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv S (SmallCrystallineDpow.SmallCrystallineAdapter.residueBase65 (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S) c) = algebraMap k S.residueRing c
    rw [residueBase65_to65]
    exact (SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv S).apply_symm_apply _

def unitReducedInv (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) :
    S.residueRing →ₐ[k] (SmallCrystallineDpow.SmallCrystallineAdapter.to62Object (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S)).residueRing where
  __ := (SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv S).symm.toRingHom
  commutes' c := by
    exact (DFunLike.congr_fun (residueBase65_to65 S) c).symm

def unitAmbient (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) :
    (SmallCrystallineDpow.SmallCrystallineAdapter.to62Object (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S)).thickening.ring →ₐ[WittVector p k] S.thickening.ring where
  __ := RingHom.id _
  commutes' _ := rfl

def unitAmbientInv (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) :
    S.thickening.ring →ₐ[WittVector p k] (SmallCrystallineDpow.SmallCrystallineAdapter.to62Object (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S)).thickening.ring where
  __ := RingHom.id _
  commutes' _ := rfl

def unitHom (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) : S ⟶ SmallCrystallineDpow.SmallCrystallineAdapter.to62Object (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S) where
  reducedMap := unitReduced S
  ambientMap := unitAmbient S
  reduction_comm a := (RingHom.quotientKerEquivOfSurjective_apply_mk
    S.thickening.reduction_surjective a).symm
  over_X := by
    change (SmallCrystallineDpow.SmallCrystallineAdapter.residueSchemeIso S).inv ≫ ((SmallCrystallineDpow.SmallCrystallineAdapter.residueSchemeIso S).hom ≫ S.immersion) = S.immersion
    exact (SmallCrystallineDpow.SmallCrystallineAdapter.residueSchemeIso S).inv_hom_id_assoc _
  dp_comp :=
    { ideal_comp := by
        change Ideal.map (RingHom.id _) (RingHom.ker (Ideal.Quotient.mk
          (RingHom.ker S.thickening.reduction))) ≤ RingHom.ker S.thickening.reduction
        rw [Ideal.map_id, Ideal.mk_ker]
      dpow_comp := by
        intro n a ha
        change S.thickening.ring at a
        exact (SmallCrystallineDpow.SmallCrystallineAdapter.quotientDP_dpow (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S) n a).symm }

def unitInv (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) : SmallCrystallineDpow.SmallCrystallineAdapter.to62Object (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S) ⟶ S where
  reducedMap := unitReducedInv S
  ambientMap := unitAmbientInv S
  reduction_comm a := (RingHom.quotientKerEquivOfSurjective_symm_apply
    S.thickening.reduction_surjective a).symm
  over_X := rfl
  dp_comp :=
    { ideal_comp := by
        change Ideal.map (RingHom.id _) (RingHom.ker S.thickening.reduction) ≤
          RingHom.ker (Ideal.Quotient.mk (RingHom.ker S.thickening.reduction))
        rw [Ideal.map_id, Ideal.mk_ker]
      dpow_comp := by
        intro n a ha
        change S.thickening.ring at a
        exact SmallCrystallineDpow.SmallCrystallineAdapter.quotientDP_dpow (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S) n a }

def unitIso (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) : S ≅ SmallCrystallineDpow.SmallCrystallineAdapter.to62Object (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S) where
  hom := unitHom S
  inv := unitInv S
  hom_inv_id := by
    apply AlgebraicGeometry.Crystalline.Cohomology.Site.Object.Hom.ext
    · apply AlgHom.ext
      intro a
      exact (SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv S).apply_symm_apply a
    · rfl
  inv_hom_id := by
    apply AlgebraicGeometry.Crystalline.Cohomology.Site.Object.Hom.ext
    · apply AlgHom.ext
      intro a
      exact (SmallCrystallineDpow.SmallCrystallineAdapter.residueEquiv S).symm_apply_apply a
    · rfl

def liftDPMap {U V : SmallCrystallineDpow.SmallCrystallineAdapter.Small65 (p := p) (k := k) (X := X)}
    (f : SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U ⟶ SmallCrystallineDpow.SmallCrystallineAdapter.to62Object V) : DividedPowers.DPMorphism V.dividedPowers U.dividedPowers where
  toRingHom := f.ambientMap.toRingHom
  ideal_comp := by
    have h := f.dp_comp.ideal_comp
    change Ideal.map f.ambientMap.toRingHom (RingHom.ker (Ideal.Quotient.mk V.ideal)) ≤
      RingHom.ker (Ideal.Quotient.mk U.ideal) at h
    simp only [Ideal.mk_ker] at h
    exact h
  dpow_comp := by
    intro n a ha
    have ha' : a ∈ RingHom.ker (Ideal.Quotient.mk V.ideal) := by
      simpa only [Ideal.mk_ker] using ha
    exact (SmallCrystallineDpow.SmallCrystallineAdapter.quotientDP_dpow U n (f.ambientMap a)).symm.trans
      ((f.dp_comp.dpow_comp a ha').trans
        (congrArg f.ambientMap (SmallCrystallineDpow.SmallCrystallineAdapter.quotientDP_dpow V n a)))

theorem liftDPMap_quotient {U V : SmallCrystallineDpow.SmallCrystallineAdapter.Small65 (p := p) (k := k) (X := X)}
    (f : SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U ⟶ SmallCrystallineDpow.SmallCrystallineAdapter.to62Object V) :
    IntegralComparison.Crystalline.Site.AffineThickening.quotientMap U V (liftDPMap f) =
      f.reducedMap.toRingHom := by
  ext x
  exact f.reduction_comm x

def liftHom {U V : SmallCrystallineDpow.SmallCrystallineAdapter.Small65 (p := p) (k := k) (X := X)}
    (f : SmallCrystallineDpow.SmallCrystallineAdapter.to62Object U ⟶ SmallCrystallineDpow.SmallCrystallineAdapter.to62Object V) : U ⟶ V where
  ringMap := liftDPMap f
  overBase := by
    ext c
    exact f.ambientMap.commutes c
  overX :=
    (congrArg (fun r => Spec.map (CommRingCat.ofHom r) ≫ V.openMap)
      (liftDPMap_quotient f)).trans f.over_X

def to62FullyFaithful : (SmallCrystallineDpow.SmallCrystallineAdapter.to62 (p := p) (k := k) (X := X)).FullyFaithful where
  preimage := liftHom
  map_preimage f := by
    apply AlgebraicGeometry.Crystalline.Cohomology.Site.Object.Hom.ext
    · apply AlgHom.ext
      intro x
      exact DFunLike.congr_fun (liftDPMap_quotient f) x
    · rfl
  preimage_map f := by
    apply IntegralComparison.Crystalline.Site.AffineThickening.Hom.ext
    rfl

instance to62IsEquivalence : (SmallCrystallineDpow.SmallCrystallineAdapter.to62 (p := p) (k := k) (X := X)).IsEquivalence where
  faithful := to62FullyFaithful.faithful
  full := to62FullyFaithful.full
  essSurj := ⟨fun S => ⟨SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S, ⟨(unitIso S).symm⟩⟩⟩

/-- The equivalence uses the actual quotient and reduction morphisms of the thickenings. -/
def equivalence : SmallCrystallineDpow.SmallCrystallineAdapter.Small65 (p := p) (k := k) (X := X) ≌ SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X) :=
  SmallCrystallineDpow.SmallCrystallineAdapter.to62.asEquivalence

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineEquivalence.SmallCrystallineAdapter
