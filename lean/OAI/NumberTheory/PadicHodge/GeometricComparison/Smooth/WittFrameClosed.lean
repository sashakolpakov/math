import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame

/-! # Witt Frame Closed -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameClosed.SmoothWittFrameClosed

noncomputable section

/-! The closed scheme of the original smooth Witt frame is its specified
special-fiber affine scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

theorem isIso : IsIso (IntegralComparison.SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n).mapToX := by
  change IsIso (Spec.map (CommRingCat.ofHom (IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p A C ρ hρ hker n).symm.toRingHom))
  exact (Scheme.Spec.mapIso
    (IntegralComparison.SmoothWitt.FrameRing.quotientEquiv p A C ρ hρ hker n).toCommRingCatIso.op).symm.isIso_hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameClosed.SmoothWittFrameClosed
