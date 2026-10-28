import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.TangentCarrierComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierData
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenCarrier

/-! # Carrier Overlap Data -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.CarrierOverlapData.Construction

noncomputable section

/-! Common labelled affine boundary models construct native overlap data with the original point and maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_modeled_carrier_overlap_data
    {β : Type} (R : CommRingCat) [IsDomain R] [IsNoetherianRing R]
    [Algebra ℂ R] [Algebra ℚ R] [Algebra.Smooth ℂ R]
    (w : β → R) (N : Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ R β w) (M : Ideal R) (z t : R) (n : ℕ)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ M n) (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ M n)
    (D E : Derivation ℂ R R) (hDz : D z = 1) (hEt : E t = 1)
    (hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ w) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ w)
    (p : PrimeSpectrum R) (hp : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ M n ≤ p.asIdeal)
    {X X' : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J H : X.IdealSheafData) (F : β → X.IdealSheafData)
    (f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (J' H' : X'.IdealSheafData) (F' : β → X'.IdealSheafData)
    [IsIntegral H.subscheme] [IsIntegral H'.subscheme]
    (a : Spec R ⟶ X) (b : Spec R ⟶ X') [IsOpenImmersion a] [IsOpenImmersion b]
    (haf : a ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (hbf : b ≫ f' = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R)
    (haJ : J.comap a = Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ M n))
    (hbJ : J'.comap b = Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ M n))
    (haH : H.comap a = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z}))
    (hbH : H'.comap b = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t}))
    (haF : ∀ l, (F l).comap a = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l}))
    (hbF : ∀ l, (F' l).comap b = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l})) :
    ∃ A : TangentCarrierData.Construction.TangentCarrierOverlapData f J H F f' J' H' F' n,
      ∃ q : A.ambient, A.left q = a p ∧ A.right q = b p ∧
        ∀ {Z : Scheme} (j : X ⟶ Z) (l : X' ⟶ Z), a ≫ j = b ≫ l → A.left ≫ j = A.right ≫ l := by
  let Hz := Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})
  let Ht := Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t})
  let : IsIntegral Hz.subscheme := Affine.OpenCarrier.Construction.affine_open_carrier_isIntegral H R a (Ideal.span {z}) haH p
    ((Ideal.span_singleton_le_iff_mem p.asIdeal).mpr (hp hz))
  let : IsIntegral Ht.subscheme := Affine.OpenCarrier.Construction.affine_open_carrier_isIntegral H' R b (Ideal.span {t}) hbH p
    ((Ideal.span_singleton_le_iff_mem p.asIdeal).mpr (hp ht))
  let : CompactSpace Hz.subscheme := QuasiCompact.compactSpace_of_compactSpace Hz.subschemeι
  let : CompactSpace Ht.subscheme := QuasiCompact.compactSpace_of_compactSpace Ht.subschemeι
  let L := Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ M n)
  let G := fun l => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l})
  have hcomp : ∀ q : Spec R, q ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) L n).support →
      Nonempty (TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) L Hz Ht G n q) := by
    intro q hq
    have hord : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ M n ≤ q.asIdeal := by
      change q ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R)
        (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ M n)) n).support at hq
      rw [ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel, HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent] at hq
      change q ∈ ((Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ M n)).support : Set (Spec (.of R))) at hq
      rw [Coefficient.ChartSupport.Construction.affineQuotientKernel_support] at hq
      exact hq
    exact TangentCarrierComparison.Construction.exists_modeled_tangent_carrier_comparison w N M z t n q hord hz ht D E hDz hEt hD hE
  let A : TangentCarrierData.Construction.TangentCarrierOverlapData f J H F f' J' H' F' n := {
    ambient := Spec R
    integral := inferInstance
    noetherian := inferInstance
    structureMap := ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R
    smooth := inferInstance
    ideal := L
    leftCarrier := Hz
    rightCarrier := Ht
    boundary := G
    left_integral := inferInstance
    right_integral := inferInstance
    left_compact := inferInstance
    right_compact := inferInstance
    left := a
    right := b
    left_etale := inferInstance
    right_etale := inferInstance
    left_ground := haf
    right_ground := hbf
    left_ideal := haJ
    right_ideal := hbJ
    left_carrier := haH
    right_carrier := hbH
    left_boundary := haF
    right_boundary := hbF
    comparison := hcomp }
  exact ⟨A, p, rfl, rfl, fun _ _ h => h⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.CarrierOverlapData.Construction
