import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ComplexMap

/-! # Frame Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameComplex

noncomputable section

/-! The actual smooth Witt frame complex is its ordinary relative de Rham complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A] (n : ℕ)

local notation "W" => WittVector p k

local instance frameAlgebra : Algebra W (FrameRing.Ring p A n) := (FrameRing.base p k A n).toAlgebra

omit [Fintype k] [CharP k p] [Module.Flat (WittVector p k) A] in
theorem ideal_eq : FrameRing.ideal p A n = Ideal.span {algebraMap W (FrameRing.Ring p A n) (p : W)} := by
  rw [FrameRing.ideal, AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.ideal, Ideal.map_span, Set.image_singleton, map_natCast, map_natCast]

def iso : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W (FrameRing.Ring p A n) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n) ≅
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W (FrameRing.Ring p A n) :=
  Principal.BaseComplex.ofIdealEq W (FrameRing.Ring p A n) (p : W)
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n)
      (ideal_eq p k A n) (FrameRing.base_isDPMorphism p k A n)

variable (C : Type u) [CommRing C] [Algebra k C] (ρ : A →+* C)
  (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))

def frameIso : RelativeFrame.ComplexMap.frameComplex
    (WittFrame.object p k A C ρ hρ hker hbase n) ≅
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W (FrameRing.Ring p A n) := iso p k A n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameComplex
