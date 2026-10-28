import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.TruncationTransition
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame

/-! # Frame Transition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransition

noncomputable section

/-! Canonical reduction morphisms between the actual smooth Witt crystalline frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p k
local notation "I" => Ideal.span {(p : A)}
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.FlatWittDividedPowers.dividedPowers p k A
local notation "Fn" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n
local notation "Fm" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase m
local notation "en" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p A C ρ hρ hker n
local notation "em" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p A C ρ hρ hker m

abbrev map : FrameRing.Ring p A m →+* FrameRing.Ring p A n := PD.TruncationTransition.map A I n m hnm

abbrev dpMap : DividedPowers.DPMorphism (FrameRing.dividedPowers p k A m) (FrameRing.dividedPowers p k A n) :=
  PD.TruncationTransition.dpMap A I δ n m hnm

omit [CharP k p] [Module.Flat (WittVector p k) A] in
theorem overBase : (FrameTransition.map p A n m hnm).comp (FrameRing.base p k A m) = FrameRing.base p k A n := by
  apply RingHom.ext
  intro w
  rfl

omit [Fact p.Prime] [Field k] [CharP k p]
  [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A] [Algebra k C] in
theorem reduction_map : (FrameRing.reduction p A C ρ hker n).comp (FrameTransition.map p A n m hnm) = FrameRing.reduction p A C ρ hker m :=
  PD.TruncationTransition.reduction_map A I n m hnm ρ hker

theorem quotientMap_eq : (en).toRingHom.comp (BigCrystallineSite.Object.quotientMap Fn Fm (dpMap p k A n m hnm)) =
    (em).toRingHom := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (en) (Ideal.Quotient.mk (FrameRing.ideal p A n) (FrameTransition.map p A n m hnm b)) =
    (em) (Ideal.Quotient.mk (FrameRing.ideal p A m) b)
  exact (FrameRing.quotientEquiv_mk p A C ρ hρ hker n (FrameTransition.map p A n m hnm b)).trans
    ((RingHom.congr_fun (reduction_map p A C ρ hker n m hnm) b).trans
      (FrameRing.quotientEquiv_mk p A C ρ hρ hker m b).symm)

def morphism : Fn ⟶ Fm where
  ringMap := dpMap p k A n m hnm
  overBase := FrameTransition.overBase p k A n m hnm
  overX := by
    change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap Fn Fm (dpMap p k A n m hnm))) ≫
      Spec.map (CommRingCat.ofHom (em).symm.toRingHom) = Spec.map (CommRingCat.ofHom (en).symm.toRingHom)
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    apply (en).injective
    change (en) (BigCrystallineSite.Object.quotientMap Fn Fm (dpMap p k A n m hnm) ((em).symm c)) = (en) ((en).symm c)
    exact (RingHom.congr_fun (quotientMap_eq p k A C ρ hρ hker hbase n m hnm) ((em).symm c)).trans
      ((em).apply_symm_apply c |>.trans ((en).apply_symm_apply c).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransition
