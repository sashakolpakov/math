import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMap

/-! # Frame Algebras -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameAlgebras

noncomputable section

/-! The actual frame morphisms retain their Witt algebra maps and original closed fibre. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ WittFrame.object p k A C ρ hρ hker hbase n)

local notation "W" => WittVector p k
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p A C ρ hρ hker n

def chartMap : letI := FrameLifting.ambientAlgebra p k C U
    A →ₐ[W] U.ring := by
  letI := FrameLifting.ambientAlgebra p k C U
  refine { β.ringMap.toRingHom.comp (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1))) with
    commutes' := ?_ }
  intro w
  exact RingHom.congr_fun β.overBase w

theorem chart_reduction (a : A) :
    Ideal.Quotient.mk U.ideal (β.ringMap (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) a)) =
      BigCrystallineCover.closedRingMap p k C U (ρ a) := by
  have hs := β.overX
  change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U F β.ringMap)) ≫
    Spec.map (CommRingCat.ofHom (e).symm.toRingHom) = U.mapToX at hs
  rw [← Spec.map_comp, ← BigCrystallineCover.closedRingMap_spec p k C U] at hs
  have he := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  have hp : (e) (Ideal.Quotient.mk (FrameRing.ideal p A n)
      (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) a)) = ρ a :=
    FrameRing.quotientEquiv_mk p A C ρ hρ hker n _
  have hi : (e).symm (ρ a) = Ideal.Quotient.mk (FrameRing.ideal p A n)
      (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) a) :=
    (e).symm_apply_eq.mpr hp.symm
  have hc := RingHom.congr_fun he (ρ a)
  change BigCrystallineSite.Object.quotientMap U F β.ringMap ((e).symm (ρ a)) = _ at hc
  rw [hi] at hc
  exact hc

variable (V : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (ζ : V ⟶ WittFrame.object p k A C ρ hρ hker hbase n) (α : V ⟶ U)

def map : letI := FrameLifting.ambientAlgebra p k C U
    letI := FrameLifting.ambientAlgebra p k C V
    U.ring →ₐ[W] V.ring := by
  letI := FrameLifting.ambientAlgebra p k C U
  letI := FrameLifting.ambientAlgebra p k C V
  exact { α.ringMap.toRingHom with commutes' := RingHom.congr_fun α.overBase }

theorem closed_agreement (a : A) :
    ζ.ringMap (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) a) -
      α.ringMap (β.ringMap (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) a)) ∈ V.ideal := by
  apply Ideal.Quotient.eq.mp
  rw [chart_reduction p k A C ρ hρ hker hbase n V ζ a]
  have hs := α.overX
  rw [← BigCrystallineCover.closedRingMap_spec p k C U,
    ← BigCrystallineCover.closedRingMap_spec p k C V] at hs
  change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V U α.ringMap)) ≫
    Spec.map (CommRingCat.ofHom (BigCrystallineCover.closedRingMap p k C U)) =
      Spec.map (CommRingCat.ofHom (BigCrystallineCover.closedRingMap p k C V)) at hs
  rw [← Spec.map_comp] at hs
  have he := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  have hc := RingHom.congr_fun he (ρ a)
  change BigCrystallineSite.Object.quotientMap V U α.ringMap (BigCrystallineCover.closedRingMap p k C U (ρ a)) =
    BigCrystallineCover.closedRingMap p k C V (ρ a) at hc
  rw [← chart_reduction p k A C ρ hρ hker hbase n U β a] at hc
  exact hc.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameAlgebras
