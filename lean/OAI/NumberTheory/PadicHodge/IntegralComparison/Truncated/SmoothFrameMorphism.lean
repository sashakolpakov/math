import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Smooth Frame Morphism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrameMorphism

noncomputable section

/-! Actual maps of smooth finite-level algebras induce the original
crystalline frame maps, with their prescribed reduction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A B : Type) [CommRing A] [CommRing B]
  [Algebra (Witt.Ring p k n) A] [Algebra (Witt.Ring p k n) B]
  [Algebra.Smooth (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) B]
  (φ : A →ₐ[Witt.Ring p k n] B)

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n

omit [Fintype k] [CharP k p]
  [Algebra.Smooth (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) B] in
theorem overBase : φ.toRingHom.comp (SmoothFrame.base p A k n) =
    SmoothFrame.base p B k n := by
  ext w
  exact φ.commutes (Witt.quotient p k n w)

def dpMap : DividedPowers.DPMorphism (SmoothDividedPowers.dividedPowers p k n A)
    (SmoothDividedPowers.dividedPowers p k n B) :=
  DividedPowers.DPMorphism.mk' (by
    apply DividedPowers.IsDPMorphism.of_comp
      (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (SmoothDividedPowers.dividedPowers p k n A)
      (SmoothDividedPowers.dividedPowers p k n B)
      (SmoothFrame.base p A k n) φ.toRingHom
      (by rw [Ideal.map_span, Set.image_singleton, map_natCast])
      (SmoothDividedPowers.wittBase_isDPMorphism p k n A)
    rw [SmoothFrameMorphism.overBase p k n A B φ]
    exact SmoothDividedPowers.wittBase_isDPMorphism p k n B)

variable (C D : Type) [CommRing C] [CommRing D] [Algebra k C] [Algebra k D]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hkerρ : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbaseρ : ∀ w : WittVector p k,
    ρ (algebraMap (Witt.Ring p k n) A (Witt.quotient p k n w)) =
    algebraMap k C (WittVector.constantCoeff w))
  (τ : B →+* D) (hτ : Function.Surjective τ) (hkerτ : RingHom.ker τ = Ideal.span {(p : B)})
  (hbaseτ : ∀ w : WittVector p k,
    τ (algebraMap (Witt.Ring p k n) B (Witt.quotient p k n w)) =
    algebraMap k D (WittVector.constantCoeff w))
  (ψ : C →ₐ[k] D) (hφ : ∀ a, τ (φ a) = ψ (ρ a))

omit [Fintype k] [CharP k p] in
theorem base_square : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C) = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k D) := by
  rw [Crystalline.Presentation.affine_wittStructureMap, Crystalline.Presentation.affine_wittStructureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext w
  exact ψ.commutes (WittVector.constantCoeff w)

local notation "FA" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.object p A C ρ hρ hkerρ k n hbaseρ
local notation "FB" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.object p B D τ hτ hkerτ k n hbaseτ
local notation "eA" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.quotientEquiv p A C ρ hρ hkerρ
local notation "eB" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.quotientEquiv p B D τ hτ hkerτ
local notation "aDP" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrameMorphism.dpMap p k n A B φ

def pulledFrame : BigCrystallineSite.Object p W (Ideal.span {(p : W)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) :=
  (BigCrystallineSite.postcompose (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (base_square p k C D ψ)).obj FB

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrameMorphism.pulledFrame p k n B C D τ hτ hkerτ hbaseτ ψ

include hφ in
omit [Fintype k] in
theorem quotientMap_eq : BigCrystallineSite.Object.quotientMap P FA aDP =
    (eB).symm.toRingHom.comp (ψ.toRingHom.comp (eA).toRingHom) := by
  apply RingHom.ext
  intro a
  change A ⧸ Ideal.span {(p : A)} at a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply (eB).injective
  change (eB) (Ideal.Quotient.mk (Ideal.span {(p : B)}) (φ x)) =
    (eB) ((eB).symm (ψ ((eA) (Ideal.Quotient.mk (Ideal.span {(p : A)}) x))))
  rw [RingEquiv.apply_symm_apply]
  exact (SmoothFrame.quotientEquiv_mk p B D τ hτ hkerτ (φ x)).trans
    ((hφ x).trans (congrArg ψ (SmoothFrame.quotientEquiv_mk p A C ρ hρ hkerρ x).symm))

def morphism : P ⟶ FA where
  ringMap := aDP
  overBase := SmoothFrameMorphism.overBase p k n A B φ
  overX := by
    change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap P FA aDP)) ≫
      Spec.map (CommRingCat.ofHom (eA).symm.toRingHom) =
        Spec.map (CommRingCat.ofHom (eB).symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    have h := RingHom.congr_fun (quotientMap_eq p k n A B φ C D
      ρ hρ hkerρ hbaseρ τ hτ hkerτ hbaseτ ψ hφ) ((eA).symm c)
    change BigCrystallineSite.Object.quotientMap P FA aDP ((eA).symm c) = (eB).symm (ψ c)
    exact h.trans (congrArg (fun z => (eB).symm (ψ z)) ((eA).apply_symm_apply c))

def boundedMorphism :
    (BoundedOpen.Equivalence.postcompose (Spec.map (CommRingCat.ofHom ψ.toRingHom))
      (base_square p k C D ψ) n).obj
        (SmoothFrame.boundedFrame p B D τ hτ hkerτ k n hbaseτ) ⟶
      SmoothFrame.boundedFrame p A C ρ hρ hkerρ k n hbaseρ :=
  ObjectProperty.homMk (morphism p k n A B φ C D ρ hρ hkerρ hbaseρ τ hτ hkerτ hbaseτ ψ hφ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrameMorphism
