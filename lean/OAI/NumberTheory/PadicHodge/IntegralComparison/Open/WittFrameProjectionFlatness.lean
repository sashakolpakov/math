import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.WittFrameLocalFlatness

/-! # Witt Frame Projection Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.WittFrameProjectionFlatness.Smooth

noncomputable section

/-! Every actual product projection along an open smooth Witt frame is flat. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p] [Finite σ]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))
  (X : Over (Spec (CommRingCat.of k)))
  (j : (Crystalline.Presentation.affineScheme k C).left ⟶ X.left) [IsOpenImmersion j]
  (hj : j ≫ X.hom = (Crystalline.Presentation.affineScheme k C).hom) (n : ℕ)
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
  (hn : (p : U.ring) ^ (n + 1) = 0)
  (P : BinaryFan U (SmoothWittFrame.frame p k A C ρ hρ hker hbase X j hj n)) (hP : IsLimit P)

include σ hn hP in
theorem projection : P.fst.ringMap.toRingHom.Flat := by
  have hrange : Set.range P.pt.mapToX ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    refine ⟨(SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n).mapToX
      (BigCrystallineSite.Object.closed.map P.snd y), ?_⟩
    exact congrArg (fun a => a y) P.snd.overX
  obtain ⟨s, hspan, hs⟩ := Crystalline.ProjectionNeighborhoods.finite_cover P.fst j hrange
  change Finset P.pt.ring at s
  apply RingHom.Flat.ofLocalizationSpanTarget P.fst.ringMap.toRingHom (s : Set P.pt.ring) hspan
  rintro ⟨a, ha⟩
  obtain ⟨r, rfl, hr⟩ := hs a ha
  exact WittFrameLocalFlatness.Smooth.localized_composite p k A C σ ρ hρ hker hbase X j hj n U hn P hP r hr

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.WittFrameProjectionFlatness.Smooth
