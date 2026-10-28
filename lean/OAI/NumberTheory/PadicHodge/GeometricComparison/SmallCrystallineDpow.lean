import OAI.AlgebraicGeometry.Crystalline.Cohomology.Site
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

/-! # Small Crystalline Dpow -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter

noncomputable section

/-! The two affine crystalline presentations retain the same ambient DP ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
  {X : Over (Spec (CommRingCat.of k))}

abbrev Small62 := AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
abbrev Small65 := IntegralComparison.Witt.Crystalline.CrystallineObject p k X

def residueEquiv (S : Small62 (p := p) (k := k) (X := X)) :
    S.thickening.ring ⧸ RingHom.ker S.thickening.reduction ≃+* S.residueRing :=
  S.thickening.reduction.quotientKerEquivOfSurjective S.thickening.reduction_surjective

def residueSchemeIso (S : Small62 (p := p) (k := k) (X := X)) :
    Spec (CommRingCat.of (S.thickening.ring ⧸ RingHom.ker S.thickening.reduction)) ≅
      Spec S.residueRing :=
  Scheme.Spec.mapIso (residueEquiv S).toCommRingCatIso.symm.op

theorem residueSchemeIso_hom (S : Small62 (p := p) (k := k) (X := X)) :
    (residueSchemeIso S).hom = Spec.map (CommRingCat.ofHom (residueEquiv S).symm.toRingHom) := rfl

theorem residueBase (S : Small62 (p := p) (k := k) (X := X)) :
    (residueEquiv S).symm.toRingHom.comp
        ((algebraMap k S.residueRing).comp (WittVector.constantCoeff : WittVector p k →+* k)) =
      (Ideal.Quotient.mk (RingHom.ker S.thickening.reduction)).comp
        (algebraMap (WittVector p k) S.thickening.ring) := by
  rw [← S.thickening.reduction_base, ← RingHom.comp_assoc]
  exact congrArg (fun f => f.comp (algebraMap (WittVector p k) S.thickening.ring))
    (RingHom.quotientKerEquivOfSurjective_symm_comp S.thickening.reduction_surjective)

def to65Object (S : Small62 (p := p) (k := k) (X := X)) : Small65 (p := p) (k := k) (X := X) where
  ring := S.thickening.ring
  base := algebraMap (WittVector p k) S.thickening.ring
  ideal := RingHom.ker S.thickening.reduction
  dividedPowers := S.thickening.dividedPowers
  baseCompatible := S.thickening.baseDP
  primeNilpotent := S.thickening.p_nilpotent
  nilIdeal := S.thickening.kernel_element_isNilpotent
  openMap := (residueSchemeIso S).hom ≫ S.immersion
  overBase := by
    change ((residueSchemeIso S).hom ≫ S.immersion) ≫
      (X.hom ≫ Spec.map (CommRingCat.ofHom WittVector.constantCoeff)) = _
    rw [Category.assoc, ← Category.assoc S.immersion, S.over_base]
    change Spec.map (CommRingCat.ofHom (residueEquiv S).symm.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k S.residueRing)) ≫
        Spec.map (CommRingCat.ofHom WittVector.constantCoeff)) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (residueBase S)

def to65DPMap {S T : Small62 (p := p) (k := k) (X := X)} (f : S ⟶ T) :
    DividedPowers.DPMorphism (to65Object T).dividedPowers (to65Object S).dividedPowers :=
  DividedPowers.DPMorphism.mk' f.dp_comp

theorem residue_naturality {S T : Small62 (p := p) (k := k) (X := X)} (f : S ⟶ T) :
    (IntegralComparison.Crystalline.Site.AffineThickening.quotientMap (to65Object S) (to65Object T)
        (to65DPMap f)).comp (residueEquiv T).symm.toRingHom =
      (residueEquiv S).symm.toRingHom.comp f.reducedMap.toRingHom := by
  ext x
  obtain ⟨a, rfl⟩ := T.thickening.reduction_surjective x
  change IntegralComparison.Crystalline.Site.AffineThickening.quotientMap (to65Object S) (to65Object T)
    (to65DPMap f) ((residueEquiv T).symm (T.thickening.reduction a)) =
      (residueEquiv S).symm (f.reducedMap (T.thickening.reduction a))
  rw [← f.reduction_comm]
  simp only [residueEquiv, RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
def to65Hom {S T : Small62 (p := p) (k := k) (X := X)} (f : S ⟶ T) :
    to65Object S ⟶ to65Object T where
  ringMap := to65DPMap f
  overBase := by
    ext a
    exact f.ambientMap.commutes a
  overX := by
    change Spec.map (CommRingCat.ofHom
      (IntegralComparison.Crystalline.Site.AffineThickening.quotientMap (to65Object S) (to65Object T)
        (to65DPMap f))) ≫ ((residueSchemeIso T).hom ≫ T.immersion) =
      (residueSchemeIso S).hom ≫ S.immersion
    have h := congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ T.immersion)
      (residue_naturality f)
    simpa only [residueSchemeIso_hom, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, f.over_X] using h

def to65 : Small62 (p := p) (k := k) (X := X) ⥤ Small65 (p := p) (k := k) (X := X) where
  obj := to65Object
  map := to65Hom
  map_id S := by apply IntegralComparison.Crystalline.Site.AffineThickening.Hom.ext; rfl
  map_comp f g := by apply IntegralComparison.Crystalline.Site.AffineThickening.Hom.ext; rfl

/-- The conversion preserves the actual ambient affine scheme, including all maps. -/
def ambientIso : to65 (p := p) (k := k) (X := X) ⋙
    IntegralComparison.Crystalline.Site.AffineThickening.ambient ≅ AlgebraicGeometry.Crystalline.Cohomology.Site.ambient p k X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp; rfl)

def residueBase65 (U : Small65 (p := p) (k := k) (X := X)) : k →+* U.ring ⧸ U.ideal :=
  (Spec.preimage (U.openMap ≫ X.hom)).hom

theorem residueBase65_spec (U : Small65 (p := p) (k := k) (X := X)) :
    Spec.map (CommRingCat.ofHom (residueBase65 U)) = U.openMap ≫ X.hom :=
  Spec.map_preimage _

theorem residueBase65_witt (U : Small65 (p := p) (k := k) (X := X)) :
    (residueBase65 U).comp (WittVector.constantCoeff : WittVector p k →+* k) =
      (Ideal.Quotient.mk U.ideal).comp U.base := by
  have h := (congrArg
    (fun t => t ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : WittVector p k →+* k)))
    (residueBase65_spec U)).trans ((Category.assoc _ _ _).trans U.overBase)
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

def quotientDP (U : Small65 (p := p) (k := k) (X := X)) :
    DividedPowers (RingHom.ker (Ideal.Quotient.mk U.ideal)) :=
  (Ideal.mk_ker (I := U.ideal)).symm ▸ U.dividedPowers

theorem transportDP_dpow {R : Type*} [CommSemiring R] {I J : Ideal R}
    (h : I = J) (δ : DividedPowers I) (n : ℕ) (a : R) :
    (h ▸ δ).dpow n a = δ.dpow n a := by
  subst J
  rfl

theorem quotientDP_dpow (U : Small65 (p := p) (k := k) (X := X)) (n : ℕ) (a : U.ring) :
    (quotientDP U).dpow n a = U.dividedPowers.dpow n a :=
  transportDP_dpow (Ideal.mk_ker (I := U.ideal)).symm U.dividedPowers n a

def to62Thickening (U : Small65 (p := p) (k := k) (X := X)) :
    letI : Algebra k (U.ring ⧸ U.ideal) := (residueBase65 U).toAlgebra
    AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening.AffinePDThickening p k (U.ring ⧸ U.ideal) := by
  let : Algebra k (U.ring ⧸ U.ideal) := (residueBase65 U).toAlgebra
  exact
    { ring := U.ring
      baseAlgebra := U.base.toAlgebra
      reduction := Ideal.Quotient.mk U.ideal
      reduction_surjective := Ideal.Quotient.mk_surjective
      reduction_base := (residueBase65_witt U).symm
      p_nilpotent := U.primeNilpotent
      dividedPowers := quotientDP U
      baseDP :=
        { ideal_comp := by
            change Ideal.map U.base _ ≤ RingHom.ker (Ideal.Quotient.mk U.ideal)
            rw [Ideal.mk_ker]
            exact U.baseCompatible.ideal_comp
          dpow_comp := by
            intro n a ha
            rw [quotientDP_dpow]
            exact U.baseCompatible.dpow_comp a ha } }

def to62Object (U : Small65 (p := p) (k := k) (X := X)) : Small62 (p := p) (k := k) (X := X) where
  residueRing := CommRingCat.of (U.ring ⧸ U.ideal)
  residueAlgebra := (residueBase65 U).toAlgebra
  thickening := to62Thickening U
  immersion := U.openMap
  over_base := (residueBase65_spec U).symm

theorem quotientMap_residueBase {U V : Small65 (p := p) (k := k) (X := X)} (f : U ⟶ V) :
    (IntegralComparison.Crystalline.Site.AffineThickening.quotientMap U V f.ringMap).comp (residueBase65 V) =
      residueBase65 U := by
  have h := congrArg (fun g => g ≫ X.hom) f.overX
  rw [Category.assoc, ← residueBase65_spec V, ← residueBase65_spec U, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

def to62Reduced {U V : Small65 (p := p) (k := k) (X := X)} (f : U ⟶ V) :
    (to62Object V).residueRing →ₐ[k] (to62Object U).residueRing where
  __ := IntegralComparison.Crystalline.Site.AffineThickening.quotientMap U V f.ringMap
  commutes' c := DFunLike.congr_fun (quotientMap_residueBase f) c

def to62Ambient {U V : Small65 (p := p) (k := k) (X := X)} (f : U ⟶ V) :
    (to62Object V).thickening.ring →ₐ[WittVector p k] (to62Object U).thickening.ring where
  __ := f.ringMap.toRingHom
  commutes' c := DFunLike.congr_fun f.overBase c

def to62Hom {U V : Small65 (p := p) (k := k) (X := X)} (f : U ⟶ V) :
    to62Object U ⟶ to62Object V where
  reducedMap := to62Reduced f
  ambientMap := to62Ambient f
  reduction_comm := fun _ => rfl
  over_X := f.overX
  dp_comp :=
    { ideal_comp := by
        change Ideal.map f.ringMap.toRingHom (RingHom.ker (Ideal.Quotient.mk V.ideal)) ≤
          RingHom.ker (Ideal.Quotient.mk U.ideal)
        rw [Ideal.mk_ker, Ideal.mk_ker]
        exact f.ringMap.ideal_comp
      dpow_comp := by
        intro n a ha
        change V.ring at a
        change a ∈ RingHom.ker (Ideal.Quotient.mk V.ideal) at ha
        change (quotientDP U).dpow n (f.ringMap a) = f.ringMap ((quotientDP V).dpow n a)
        rw [quotientDP_dpow, quotientDP_dpow]
        exact f.ringMap.dpow_comp a (by simpa only [Ideal.mk_ker] using ha) }

def to62 : Small65 (p := p) (k := k) (X := X) ⥤ Small62 (p := p) (k := k) (X := X) where
  obj := to62Object
  map := to62Hom
  map_id U := by
    apply AlgebraicGeometry.Crystalline.Cohomology.Site.Object.Hom.ext
    · apply AlgHom.ext
      intro x
      change U.ring ⧸ U.ideal at x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    · rfl
  map_comp {U V W} f g := by
    apply AlgebraicGeometry.Crystalline.Cohomology.Site.Object.Hom.ext
    · apply AlgHom.ext
      intro x
      change W.ring ⧸ W.ideal at x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    · rfl

def ambientIso62 : to62 (p := p) (k := k) (X := X) ⋙
    AlgebraicGeometry.Crystalline.Cohomology.Site.ambient p k X ≅ IntegralComparison.Crystalline.Site.AffineThickening.ambient :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp; rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter
