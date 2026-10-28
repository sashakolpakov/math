import OAI.NumberTheory.PadicHodge.GeometricComparison.WittDividedPowerNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Witt Frame Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap

noncomputable section

/-! Compatible maps of actual flat Witt lifts induce morphisms of their original
bounded crystalline frames over the corresponding special-fiber morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

universe u
variable (p : ℕ) [Fact p.Prime] (k A B C D : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing B] [Algebra (WittVector p k) B] [Module.Flat (WittVector p k) B]
  [CommRing C] [Algebra k C] [CommRing D] [Algebra k D]
  (ρA : A →+* C) (hsA : Function.Surjective ρA) (hkA : RingHom.ker ρA = Ideal.span {(p : A)})
  (hbA : ∀ w : WittVector p k, ρA (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))
  (ρB : B →+* D) (hsB : Function.Surjective ρB) (hkB : RingHom.ker ρB = Ideal.span {(p : B)})
  (hbB : ∀ w : WittVector p k, ρB (algebraMap (WittVector p k) B w) =
    algebraMap k D (WittVector.constantCoeff w))
  (α : A →ₐ[WittVector p k] B) (β : C →+* D)
  (hρ : ∀ a, ρB (α a) = β (ρA a))
  (g : (IntegralComparison.Crystalline.Presentation.affineScheme k D).left ⟶ (IntegralComparison.Crystalline.Presentation.affineScheme k C).left)
  (hg : g ≫ IntegralComparison.Witt.Crystalline.wittStructureMap p k (IntegralComparison.Crystalline.Presentation.affineScheme k C) = IntegralComparison.Witt.Crystalline.wittStructureMap p k (IntegralComparison.Crystalline.Presentation.affineScheme k D))
  (hβ : g = Spec.map (CommRingCat.ofHom β)) (n : ℕ)

local notation "FA" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k A C ρA hsA hkA hbA n
local notation "FB" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k B D ρB hsB hkB hbB n
local notation "GB" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose g hg) FB
local notation "eA" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p A C ρA hsA hkA n
local notation "eB" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p B D ρB hsB hkB n

def integralDPMap : DividedPowers.DPMorphism
    (IntegralComparison.FlatWittDividedPowers.dividedPowers p k A) (IntegralComparison.FlatWittDividedPowers.dividedPowers p k B) where
  toRingHom := α.toRingHom
  ideal_comp := (WittDividedPowerNaturality.FlatWittDividedPowerNaturality.isDPMorphism p k A B α.toRingHom).ideal_comp
  dpow_comp := (WittDividedPowerNaturality.FlatWittDividedPowerNaturality.isDPMorphism p k A B α.toRingHom).dpow_comp

def frameDPMap : DividedPowers.DPMorphism (IntegralComparison.SmoothWitt.FrameRing.dividedPowers p k A n) (IntegralComparison.SmoothWitt.FrameRing.dividedPowers p k B n) :=
  PDTruncationFunctor.PDTruncationMap.dpMap (integralDPMap p k A B α) n

def residueMap : (IntegralComparison.SmoothWitt.FrameRing.Ring p A n ⧸ IntegralComparison.SmoothWitt.FrameRing.ideal p A n) →+* (IntegralComparison.SmoothWitt.FrameRing.Ring p B n ⧸ IntegralComparison.SmoothWitt.FrameRing.ideal p B n) :=
  Ideal.quotientMap (IntegralComparison.SmoothWitt.FrameRing.ideal p B n) (frameDPMap p k A B α n).toRingHom
    (Ideal.map_le_iff_le_comap.mp (frameDPMap p k A B α n).ideal_comp)

include hρ in
omit [Algebra k C] [Algebra k D] in
theorem residueMap_eq : (eB).toRingHom.comp (residueMap p k A B α n) = β.comp (eA).toRingHom := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change eB (Ideal.Quotient.mk (IntegralComparison.SmoothWitt.FrameRing.ideal p B n)
      (PDTruncationFunctor.PDTruncationMap.map (integralDPMap p k A B α) n b)) =
    β (eA (Ideal.Quotient.mk (IntegralComparison.SmoothWitt.FrameRing.ideal p A n) b))
  rw [IntegralComparison.SmoothWitt.FrameRing.quotientEquiv_mk, IntegralComparison.SmoothWitt.FrameRing.quotientEquiv_mk]
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact hρ a

include hρ in
theorem quotientMap_eq : (eB).toRingHom.comp (IntegralComparison.BigCrystallineSite.Object.quotientMap GB FA
    (frameDPMap p k A B α n)) = β.comp (eA).toRingHom :=
  residueMap_eq p k A B C D ρA hsA hkA ρB hsB hkB α β hρ n

def morphism : GB ⟶ FA where
  ringMap := frameDPMap p k A B α n
  overBase := by
    apply RingHom.ext
    intro w
    change Ideal.Quotient.mk ((Ideal.span {(p : B)}) ^ (n + 1)) (α (algebraMap (WittVector p k) A w)) =
      Ideal.Quotient.mk ((Ideal.span {(p : B)}) ^ (n + 1)) (algebraMap (WittVector p k) B w)
    rw [α.commutes]
  overX := by
    change Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap GB FA
        (frameDPMap p k A B α n))) ≫
      Spec.map (CommRingCat.ofHom (eA).symm.toRingHom) =
        Spec.map (CommRingCat.ofHom (eB).symm.toRingHom) ≫ g
    conv_rhs => rw [hβ]
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    apply (eB).injective
    change eB (IntegralComparison.BigCrystallineSite.Object.quotientMap GB FA
        (frameDPMap p k A B α n) ((eA).symm c)) =
      eB ((eB).symm (β c))
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.congr_fun
      (quotientMap_eq p k A B C D ρA hsA hkA hbA ρB hsB hkB hbB α β hρ g hg n) ((eA).symm c)).trans
        (congrArg β ((eA).apply_symm_apply c))

def boundedMorphism :
    (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj
      (IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k B D ρB hsB hkB hbB n) ⟶
        IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρA hsA hkA hbA n :=
  ObjectProperty.homMk (morphism p k A B C D ρA hsA hkA hbA ρB hsB hkB hbB α β hρ g hg hβ n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap
