import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCover
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothNil

/-! # Frame Algebras -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.SmoothLifting

/-! Every original bounded crystalline thickening receives a morphism
to the frame of an actual smooth lift over the same finite Witt level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C : Type) [CommRing A] [CommRing C]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A] [Algebra k C]
  (ρ : A →+* C)
  (hbase : ∀ w : WittVector p k,
    ρ ((algebraMap (Witt.Ring p k n) A) (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))
  (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittBase.truncatedBase p k U.obj n U.property

@[instance_reducible] def ambientAlgebra : Algebra S U.obj.ring := (b).toAlgebra

def closedMap : letI := ambientAlgebra p k n C U; A →ₐ[S] U.obj.ring ⧸ U.obj.ideal := by
  letI := ambientAlgebra p k n C U
  refine { (BigCrystallineCover.closedRingMap p k C U.obj).comp ρ with commutes' := ?_ }
  intro s
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective s
  change BigCrystallineCover.closedRingMap p k C U.obj
    (ρ (algebraMap S A (Witt.quotient p k n w))) =
      Ideal.Quotient.mk U.obj.ideal (U.obj.base w)
  rw [hbase]
  exact RingHom.congr_fun (BigCrystallineCover.closedRingMap_coefficients p k C U.obj) w

omit [Fintype k] in
include hbase in
theorem exists_lift : ∃ l : A →+* U.obj.ring,
    (Ideal.Quotient.mk U.obj.ideal).comp l =
      (BigCrystallineCover.closedRingMap p k C U.obj).comp ρ ∧
        l.comp (SmoothFrame.base p A k n) = U.obj.base := by
  let := ambientAlgebra p k n C U
  obtain ⟨l, hl⟩ := AlgebraicGeometry.Crystalline.Cohomology.SmoothNil.SmoothNilLifting.exists_lift
    (closedMap p k n A C ρ hbase U) (Ideal.Quotient.mkₐ S U.obj.ideal)
    Ideal.Quotient.mk_surjective
    (fun a ha => U.obj.nilIdeal a (Ideal.Quotient.eq_zero_iff_mem.mp ha))
  refine ⟨l.toRingHom, congrArg AlgHom.toRingHom hl, ?_⟩
  apply RingHom.ext
  intro w
  exact l.commutes (Witt.quotient p k n w)

variable (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (l : A →+* U.obj.ring)
  (hl : (Ideal.Quotient.mk U.obj.ideal).comp l =
    (BigCrystallineCover.closedRingMap p k C U.obj).comp ρ)
  (hb : l.comp (SmoothFrame.base p A k n) = U.obj.base)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.object p A C ρ hρ hker k n hbase
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.quotientEquiv p A C ρ hρ hker

include hb in
omit [Fintype k] in
theorem map_isDPMorphism :
    DividedPowers.IsDPMorphism (SmoothDividedPowers.dividedPowers p k n A)
      U.obj.dividedPowers l := by
  apply DividedPowers.IsDPMorphism.of_comp
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (SmoothDividedPowers.dividedPowers p k n A) U.obj.dividedPowers
    (SmoothFrame.base p A k n) l
    (by rw [Ideal.map_span, Set.image_singleton, map_natCast])
    (SmoothDividedPowers.wittBase_isDPMorphism p k n A)
  rw [hb]
  exact U.obj.baseCompatible

def ringMap : DividedPowers.DPMorphism (F).dividedPowers U.obj.dividedPowers :=
  DividedPowers.DPMorphism.mk' (map_isDPMorphism p k n A C U l hb)

include hl in
omit [Fintype k] in
theorem quotientMap_eq :
    BigCrystallineSite.Object.quotientMap U.obj F (SmoothLifting.ringMap p k n A C ρ hbase U hρ hker l hb) =
      (BigCrystallineCover.closedRingMap p k C U.obj).comp (e).toRingHom := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk U.obj.ideal (l a) =
    BigCrystallineCover.closedRingMap p k C U.obj
      ((e) (Ideal.Quotient.mk (Ideal.span {(p : A)}) a))
  exact (RingHom.congr_fun hl (a : A)).trans
    (congrArg (BigCrystallineCover.closedRingMap p k C U.obj)
      (SmoothFrame.quotientEquiv_mk p A C ρ hρ hker (a : A))).symm

def morphism : U.obj ⟶ F where
  ringMap := SmoothLifting.ringMap p k n A C ρ hbase U hρ hker l hb
  overBase := hb
  overX := by
    change Spec.map (CommRingCat.ofHom
      (BigCrystallineSite.Object.quotientMap U.obj F (SmoothLifting.ringMap p k n A C ρ hbase U hρ hker l hb))) ≫
        Spec.map (CommRingCat.ofHom (e).symm.toRingHom) = U.obj.mapToX
    rw [← Spec.map_comp]
    have he : (BigCrystallineSite.Object.quotientMap U.obj F (SmoothLifting.ringMap p k n A C ρ hbase U hρ hker l hb)).comp
        (e).symm.toRingHom = BigCrystallineCover.closedRingMap p k C U.obj := by
      rw [quotientMap_eq p k n A C ρ hbase U hρ hker l hl hb]
      ext c
      exact congrArg (BigCrystallineCover.closedRingMap p k C U.obj)
        ((e).apply_symm_apply c)
    change Spec.map (CommRingCat.ofHom
      ((BigCrystallineSite.Object.quotientMap U.obj F (SmoothLifting.ringMap p k n A C ρ hbase U hρ hker l hb)).comp
        (e).symm.toRingHom)) = _
    rw [he]
    exact BigCrystallineCover.closedRingMap_spec p k C U.obj

omit [Fintype k] in
theorem exists_morphism : Nonempty (U ⟶ SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase) := by
  obtain ⟨l, hl, hb⟩ := exists_lift p k n A C ρ hbase U
  exact ⟨ObjectProperty.homMk (morphism p k n A C ρ hbase U hρ hker l hl hb)⟩

end NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras.SmoothLifting

namespace NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras

/-! Maps to an actual finite-level smooth frame carry the truncated
Witt algebra structure and the prescribed closed-fiber map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C : Type) [CommRing A] [CommRing C]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Witt.Ring p k n) A (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ SmoothFrame.object p A C ρ hρ hker k n hbase)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.object p A C ρ hρ hker k n hbase
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.quotientEquiv p A C ρ hρ hker

include β in
omit [Fintype k] in
theorem frame_property : (p : U.ring) ^ (n + 1) = 0 := by
  have hz : (p : (F).ring) ^ (n + 1) = 0 :=
    SmoothFrame.prime_power_zero p A k n
  simpa only [map_pow, map_natCast, map_zero] using
    congrArg β.ringMap.toRingHom hz

@[instance_reducible] def ambientAlgebra : Algebra S U.ring :=
  (Bounded.WittBase.truncatedBase p k U n
    (frame_property p k n A C ρ hρ hker hbase U β)).toAlgebra

def chartMap : letI := ambientAlgebra p k n A C ρ hρ hker hbase U β;
    A →ₐ[S] U.ring := by
  letI := ambientAlgebra p k n A C ρ hρ hker hbase U β
  refine { β.ringMap.toRingHom with commutes' := ?_ }
  intro s
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective s
  exact RingHom.congr_fun β.overBase w

omit [Fintype k] in
theorem chart_reduction (a : A) :
    Ideal.Quotient.mk U.ideal (β.ringMap a) =
      BigCrystallineCover.closedRingMap p k C U (ρ a) := by
  have hs := β.overX
  change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U F β.ringMap)) ≫
    Spec.map (CommRingCat.ofHom (e).symm.toRingHom) = U.mapToX at hs
  rw [← Spec.map_comp, ← BigCrystallineCover.closedRingMap_spec p k C U] at hs
  have he := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  have hi : (e).symm (ρ a) = Ideal.Quotient.mk (Ideal.span {(p : A)}) a :=
    (e).symm_apply_eq.mpr
      (SmoothFrame.quotientEquiv_mk p A C ρ hρ hker a).symm
  have hc := RingHom.congr_fun he (ρ a)
  change BigCrystallineSite.Object.quotientMap U F β.ringMap ((e).symm (ρ a)) = _ at hc
  rw [hi] at hc
  exact hc

variable (V : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (ζ : V ⟶ SmoothFrame.object p A C ρ hρ hker k n hbase) (α : V ⟶ U)

def map : letI := ambientAlgebra p k n A C ρ hρ hker hbase U β;
    letI := ambientAlgebra p k n A C ρ hρ hker hbase V ζ;
    U.ring →ₐ[S] V.ring := by
  letI := ambientAlgebra p k n A C ρ hρ hker hbase U β
  letI := ambientAlgebra p k n A C ρ hρ hker hbase V ζ
  refine { α.ringMap.toRingHom with commutes' := ?_ }
  intro s
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective s
  exact RingHom.congr_fun α.overBase w

omit [Fintype k] in
theorem closed_agreement (a : A) : ζ.ringMap a - α.ringMap (β.ringMap a) ∈ V.ideal := by
  apply Ideal.Quotient.eq.mp
  rw [chart_reduction p k n A C ρ hρ hker hbase V ζ a]
  have hs := α.overX
  rw [← BigCrystallineCover.closedRingMap_spec p k C U,
    ← BigCrystallineCover.closedRingMap_spec p k C V] at hs
  change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V U α.ringMap)) ≫
    Spec.map (CommRingCat.ofHom (BigCrystallineCover.closedRingMap p k C U)) =
      Spec.map (CommRingCat.ofHom (BigCrystallineCover.closedRingMap p k C V)) at hs
  rw [← Spec.map_comp] at hs
  have he := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  have hc := RingHom.congr_fun he (ρ a)
  change BigCrystallineSite.Object.quotientMap V U α.ringMap
    (BigCrystallineCover.closedRingMap p k C U (ρ a)) =
      BigCrystallineCover.closedRingMap p k C V (ρ a) at hc
  rw [← chart_reduction p k n A C ρ hρ hker hbase U β a] at hc
  exact hc.symm

end NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras

end

end OAI
