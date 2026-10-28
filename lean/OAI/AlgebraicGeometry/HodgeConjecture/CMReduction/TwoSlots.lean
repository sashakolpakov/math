import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalTopSwitch
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.SelectSlots
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedPermutation

/-! # Two Slots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.TwoSlots.CM.Construction

noncomputable section

/-! A switch of two marked tuple entries, with every residual entry
pulled back from the target variety. -/

open _root_.CategoryTheory

theorem two_slot_contraction
    (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput) (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput) (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (r : ℕ)
    (a b : Fin ((r + 1) + (r + 1))) (hab : a ≠ b)
    (x : Fin ((r + 1) + (r + 1)) →
      (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.complexCohomology 1)
    (y : Fin ((r + 1) + (r + 1)) → X.variety.complexCohomology 1)
    (hrest : ∀ i, i ≠ a → i ≠ b → x i =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (Bridge.CM.Construction.bridgeBase R₁.abelianVariety R₂.abelianVariety X) (y i))
    (hxa : x a = Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1
      (Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X)
      (Endpoints.CM.Construction.realizedVector E R₁ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))
    (hxb : x b = Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1
      (Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X)
      (Endpoints.CM.Construction.realizedVector E R₂ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))
    (hprevious : PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
      (PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).toOver) (r + 1) x))
    (hswitch : PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
      (Bridge.CM.Construction.switchPacked E R₁ R₂ X (y a) (y b))) :
    PackedRegroup.CM.Construction.IsAlgebraicEven X.variety (PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace X.toOver) (r + 1) y) := by
  let W : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X
  let f : W.toOver ⟶ X.toOver := Bridge.CM.Construction.bridgeBase R₁.abelianVariety R₂.abelianVariety X
  let F : X.variety.complexCohomology 1 → W.variety.complexCohomology 1 :=
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f
  obtain ⟨σ, u, hx, hy⟩ := SelectSlots.CM.Construction.select_two_slots_map F r a b hab x y hrest
  have hp := (PackedPermutation.CM.Construction.packH1Cup_perm_algebraic_iff hexterior W (r + 1) x σ).mpr hprevious
  rw [hx, PackedRegroup.CM.Construction.packH1Cup_evenAppend, PackedRegroup.CM.Construction.packH1Cup_pair, hxa, hxb] at hp
  have hpull : PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace W.toOver) r (F ∘ u) =
      PackedRegroup.CM.Construction.evenPullback f (PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace X.toOver) r u) :=
    (PackedRegroup.CM.Construction.evenPullback_H1Cup f r u).symm
  rw [hpull] at hp
  have hc := LocalTopSwitch.CM.Construction.local_switch_contraction h_Functoriality h_LineBundleCycles h_ThomClass h_PolarizedPairing hlefschetz E v₁ v₂ R₁ R₂ X
    (PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace X.toOver) r u) (y a) (y b) hp hswitch
  apply (PackedPermutation.CM.Construction.packH1Cup_perm_algebraic_iff hexterior X (r + 1) y σ).mp
  rw [hy, PackedRegroup.CM.Construction.packH1Cup_evenAppend, PackedRegroup.CM.Construction.packH1Cup_pair]
  exact hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.TwoSlots.CM.Construction
