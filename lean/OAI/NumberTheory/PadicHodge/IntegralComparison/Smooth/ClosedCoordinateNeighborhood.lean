import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedConormalNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.AffineNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothRelativeRank
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateRank
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover

/-! # Closed Coordinate Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCoordinateNeighborhood

noncomputable section

/-! A smooth closed subscheme has actual ambient affine neighborhoods
with regular equations, matching conormal bases, and native étale
coordinates on the closed subscheme. All basis ranks come from geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsClosedImmersion f.left] [IsLocallyNoetherian Y.left] [IsProper X.hom]
  (N g : ℕ) [SmoothOfRelativeDimension N Y.hom] [SmoothOfRelativeDimension g X.hom]

theorem exists_neighborhood (U : Y.left.Opens) (x : X.left) (hx : f.left x ∈ U) :
    ∃ (V : Y.left.Opens) (hV : IsAffineOpen V), V ≤ U ∧ f.left x ∈ V ∧
      ∃ (τ : Type u) (_ : Fintype τ)
        (a : Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V))),
        (letI := a
         IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) ∧
           Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V))) ∧
        ∃ (c : ℕ) (s : Fin c → Γ(Y.left, V))
          (hs : Koszul.OrientedTopCohomology.ideal Γ(Y.left, V) s = f.left.ker.ideal ⟨V, hV⟩),
          RingTheory.Sequence.IsRegular Γ(Y.left, V) (List.ofFn s) ∧
          ∃ b : Module.Basis (Fin c) (Γ(Y.left, V) ⧸ f.left.ker.ideal ⟨V, hV⟩)
              (f.left.ker.ideal ⟨V, hV⟩).Cotangent,
            (∀ j, b j = (f.left.ker.ideal ⟨V, hV⟩).toCotangent
              (ConormalKoszulPurity.conormalVectors Γ(Y.left, V)
                (f.left.ker.ideal ⟨V, hV⟩) s hs j)) ∧ c = N - g ∧
            Nonempty (Module.Basis (Fin g) (Intrinsic.SmoothClosedSections.ring R Y V ⧸ f.left.ker.ideal ⟨V, hV⟩)
              Ω[Intrinsic.SmoothClosedSections.ring R Y V ⧸ f.left.ker.ideal ⟨V, hV⟩⁄R]) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : SmoothOfRelativeDimension g (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  obtain ⟨a, hxa⟩ := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.covers R X x
  let C := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing R X a
  let chart := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap R X a
  obtain ⟨U₀, hU₀, hx₀, hU₀U, hU₀C⟩ :=
    Closed.AffineNeighborhood.exists_subopen f.left U chart.opensRange x hx hxa
  let : IsNoetherianRing Γ(Y.left, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  obtain ⟨V, hV, hVU₀, hxV, c, s, hs, hr, b, hb, hc⟩ :=
    ClosedConormalNeighborhood.exists_neighborhood f.left Y.hom N g U₀ hU₀ x hx₀
  have hVC : f.left ⁻¹ᵁ V ≤ chart.opensRange := (f.left.preimage_mono hVU₀).trans hU₀C
  let τ := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X a
  let sourceA : Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) :=
    AffineOpen.EtaleCoordinates.polynomialAlgebra R X (f.left ⁻¹ᵁ V) (hV.preimage f.left)
      C chart hVC τ
  let := sourceA
  have sourceTower : IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) :=
    AffineOpen.EtaleCoordinates.tower R X (f.left ⁻¹ᵁ V) (hV.preimage f.left)
      C chart hVC τ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_over R X a)
  let := sourceTower
  have sourceEtale : Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) :=
    AffineOpen.EtaleCoordinates.etale R X (f.left ⁻¹ᵁ V) (hV.preimage f.left) C chart hVC τ
  let := sourceEtale
  let Q := Intrinsic.SmoothClosedSections.ring R Y V ⧸ f.left.ker.ideal ⟨V, hV⟩
  let e := Intrinsic.SmoothClosedSections.quotientEquiv R X Y f V hV
  let : Algebra (MvPolynomial τ R) Q :=
    IntegralComparison.Etale.CoordinateTransport.polynomialAlgebra R (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) Q τ e.symm
  let : IsScalarTower R (MvPolynomial τ R) Q :=
    IntegralComparison.Etale.CoordinateTransport.tower R (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) Q τ e.symm
  let : Algebra.Etale (MvPolynomial τ R) Q :=
    IntegralComparison.Etale.CoordinateTransport.etale R (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) Q τ e.symm
  let q : PrimeSpectrum (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ V)) := (hV.preimage f.left).primeIdealOf ⟨x, hxV⟩
  let p : PrimeSpectrum Q := q.comap e.toRingHom
  refine ⟨V, hV, hVU₀.trans hU₀U, hxV, τ, inferInstance, sourceA,
    ⟨sourceTower, sourceEtale⟩, c, s, hs, hr, b, hb, hc, ?_⟩
  exact ⟨IntegralComparison.Etale.CoordinateRank.basis R Q τ p g
    (Intrinsic.SmoothRelativeRank.quotient R X Y f g V hV p)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCoordinateNeighborhood
