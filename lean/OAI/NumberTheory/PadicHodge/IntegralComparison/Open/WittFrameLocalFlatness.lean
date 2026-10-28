import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProductLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProductFlatnessTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProjectionNeighborhoods

/-! # Witt Frame Local Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.WittFrameLocalFlatness.Smooth

noncomputable section

/-! Actual product projections are flat on principal neighborhoods contained in a smooth Witt chart. -/

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
theorem localized_projection (r : U.ring) (hr : Set.range (Crystalline.Localization.object U r).mapToX ⊆ Set.range j) :
    (Crystalline.ProductLocalization.cone P r).fst.ringMap.toRingHom.Flat := by
  let V := Crystalline.Localization.object U r
  let t := IsOpenImmersion.lift j V.mapToX hr
  have ht : t ≫ j = V.mapToX := IsOpenImmersion.lift_fac j V.mapToX hr
  have hv : (p : V.ring) ^ (n + 1) = 0 :=
    BoundedCrystalline.Site.property_of_hom (Witt.Crystalline.wittStructureMap p k X) n (Crystalline.Localization.hom U r) hn
  let : Fintype σ := Fintype.ofFinite σ
  let : Algebra.Smooth (WittVector p k) (MvPolynomial σ (WittVector p k)) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth (WittVector p k) A :=
    Algebra.Smooth.comp (WittVector p k) (MvPolynomial σ (WittVector p k)) A
  obtain ⟨α⟩ := SmoothWittFrame.exists_map p k A C ρ hρ hker hbase X j hj n V t ht hv
  exact Crystalline.ProductFlatnessTransport.fst (Crystalline.ProductLocalization.cone P r)
    (SmoothWittFrameProduct.cone p k A C σ ρ hρ hker hbase X j hj n V α)
    (Crystalline.ProductLocalization.isProduct P hP r)
    (SmoothWittFrameProduct.isProduct p k A C σ ρ hρ hker hbase X j hj n V α)
    (SmoothWittFrameProduct.projection_flat p k A C σ ρ hρ hker hbase X j hj n V α)

include σ hn hP in
theorem localized_composite (r : U.ring) (hr : Set.range (Crystalline.Localization.object U r).mapToX ⊆ Set.range j) :
    (Crystalline.Localization.hom P.pt (P.fst.ringMap r) ≫ P.fst).ringMap.toRingHom.Flat := by
  have hbaseFlat : (algebraMap U.ring (Crystalline.Localization.Ring U r)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers r))
  have h := hbaseFlat.comp (localized_projection p k A C σ ρ hρ hker hbase X j hj n U hn P hP r hr)
  have he := congrArg (fun a : (Crystalline.ProductLocalization.cone P r).pt ⟶ U => a.ringMap.toRingHom)
    (Crystalline.LocalizationMaps.localizedHom_square P.fst r)
  exact he ▸ h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.WittFrameLocalFlatness.Smooth
