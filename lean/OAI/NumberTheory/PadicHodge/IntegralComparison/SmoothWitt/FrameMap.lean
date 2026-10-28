import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameLifting

/-! # Frame Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMap

noncomputable section

/-! Compatible smooth lifts give actual morphisms to the original bounded crystalline frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (hn : (p : U.ring) ^ (n + 1) = 0) (l : A →+* U.ring)
  (hl : (Ideal.Quotient.mk U.ideal).comp l = (BigCrystallineCover.closedRingMap p k C U).comp ρ)
  (hb : l.comp (algebraMap (WittVector p k) A) = U.base)

local notation "W" => WittVector p k
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p A C ρ hρ hker n

def map : FrameRing.Ring p A n →+* U.ring :=
  Ideal.Quotient.lift _ l (by
    change (Ideal.span {(p : A)}) ^ (n + 1) ≤ RingHom.ker l
    rw [Ideal.span_singleton_pow, Ideal.span_le]
    rintro x (rfl : x = _)
    change l ((p : A) ^ (n + 1)) = 0
    rw [map_pow, map_natCast, hn])

omit [Fintype k] [Module.Flat (WittVector p k) A] in
include hb in
theorem overBase : (FrameMap.map p k A C n U hn l).comp (FrameRing.base p k A n) = U.base := by
  apply RingHom.ext
  intro w
  exact RingHom.congr_fun hb w

omit [Fintype k] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A] in
include hl in
theorem reduction : (Ideal.Quotient.mk U.ideal).comp (FrameMap.map p k A C n U hn l) =
    (BigCrystallineCover.closedRingMap p k C U).comp (FrameRing.reduction p A C ρ hker n) := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact RingHom.congr_fun hl b

omit [Fintype k] in
include hb in
theorem map_isDPMorphism : DividedPowers.IsDPMorphism (FrameRing.dividedPowers p k A n) U.dividedPowers
    (FrameMap.map p k A C n U hn l) := by
  apply DividedPowers.IsDPMorphism.of_comp
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (FrameRing.dividedPowers p k A n) U.dividedPowers
      (FrameRing.base p k A n) (FrameMap.map p k A C n U hn l)
      (by simp only [FrameRing.ideal, AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.ideal, Ideal.map_span, Set.image_singleton, map_natCast])
      (FrameRing.base_isDPMorphism p k A n)
  rw [FrameMap.overBase p k A C n U hn l hb]
  exact U.baseCompatible

def ringMap : DividedPowers.DPMorphism (FrameRing.dividedPowers p k A n) U.dividedPowers where
  toRingHom := FrameMap.map p k A C n U hn l
  ideal_comp := (map_isDPMorphism p k A C n U hn l hb).ideal_comp
  dpow_comp := (map_isDPMorphism p k A C n U hn l hb).dpow_comp

omit [Fintype k] in
include hl in
theorem quotientMap_eq : BigCrystallineSite.Object.quotientMap U F (FrameMap.ringMap p k A C n U hn l hb) =
    (BigCrystallineCover.closedRingMap p k C U).comp (e).toRingHom := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk U.ideal (FrameMap.map p k A C n U hn l b) =
    BigCrystallineCover.closedRingMap p k C U ((e) (Ideal.Quotient.mk (FrameRing.ideal p A n) b))
  exact (RingHom.congr_fun (reduction p k A C ρ hker n U hn l hl) b).trans
    (congrArg (BigCrystallineCover.closedRingMap p k C U)
      (FrameRing.quotientEquiv_mk p A C ρ hρ hker n b).symm)

def morphism : U ⟶ F where
  ringMap := FrameMap.ringMap p k A C n U hn l hb
  overBase := FrameMap.overBase p k A C n U hn l hb
  overX := by
    change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U F (FrameMap.ringMap p k A C n U hn l hb))) ≫
      Spec.map (CommRingCat.ofHom (e).symm.toRingHom) = U.mapToX
    rw [← Spec.map_comp]
    have he : (BigCrystallineSite.Object.quotientMap U F (FrameMap.ringMap p k A C n U hn l hb)).comp (e).symm.toRingHom =
        BigCrystallineCover.closedRingMap p k C U := by
      rw [quotientMap_eq p k A C ρ hρ hker hbase n U hn l hl hb]
      apply RingHom.ext
      intro c
      change BigCrystallineCover.closedRingMap p k C U ((e) ((e).symm c)) = _
      rw [RingEquiv.apply_symm_apply]
    change Spec.map (CommRingCat.ofHom
      ((BigCrystallineSite.Object.quotientMap U F (FrameMap.ringMap p k A C n U hn l hb)).comp (e).symm.toRingHom)) = _
    rw [he]
    exact BigCrystallineCover.closedRingMap_spec p k C U

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMap
