import OAI.AlgebraicGeometry.HodgeConjecture.Kunneth
import OAI.AlgebraicGeometry.HodgeConjecture.Products

/-! # Four Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.FourProduct.CM.SurfaceConstruction

noncomputable section

/-! Grouping the given four-factor categorical product into two binary
products, and proving nonvanishing of the literal fourfold class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

variable {A : Fin 4 → Over Foundations.Scheme.ProjectiveSpace.complexBase} {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  (π : ∀ i, X ⟶ A i)

def firstPairMap : X ⟶ A 0 ⊗ A 1 := lift (π 0) (π 1)
def lastPairMap : X ⟶ A 2 ⊗ A 3 := lift (π 2) (π 3)

private def groupedLegs {T : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : T ⟶ A 0 ⊗ A 1) (g : T ⟶ A 2 ⊗ A 3) : ∀ i : Fin 4, T ⟶ A i :=
  Fin.cons (f ≫ fst _ _) (Fin.cons (f ≫ snd _ _)
    (Fin.cons (g ≫ fst _ _) (Fin.cons (g ≫ snd _ _) (fun i => i.elim0))))

def fourProduct_isBinaryProduct (hprod : IsLimit (Fan.mk X π)) :
    IsLimit (BinaryFan.mk (firstPairMap π) (lastPairMap π)) := by
  refine BinaryFan.IsLimit.mk _ (fun f g => Fan.IsLimit.lift hprod (groupedLegs f g)) ?_ ?_ ?_
  · intro T f g
    apply CartesianMonoidalCategory.hom_ext
    · change (Fan.IsLimit.lift hprod (groupedLegs f g) ≫ lift (π 0) (π 1)) ≫ fst _ _ = _
      rw [Category.assoc, CartesianMonoidalCategory.lift_fst]
      exact Fan.IsLimit.fac hprod (groupedLegs f g) 0
    · change (Fan.IsLimit.lift hprod (groupedLegs f g) ≫ lift (π 0) (π 1)) ≫ snd _ _ = _
      rw [Category.assoc, CartesianMonoidalCategory.lift_snd]
      exact Fan.IsLimit.fac hprod (groupedLegs f g) 1
  · intro T f g
    apply CartesianMonoidalCategory.hom_ext
    · change (Fan.IsLimit.lift hprod (groupedLegs f g) ≫ lift (π 2) (π 3)) ≫ fst _ _ = _
      rw [Category.assoc, CartesianMonoidalCategory.lift_fst]
      exact Fan.IsLimit.fac hprod (groupedLegs f g) 2
    · change (Fan.IsLimit.lift hprod (groupedLegs f g) ≫ lift (π 2) (π 3)) ≫ snd _ _ = _
      rw [Category.assoc, CartesianMonoidalCategory.lift_snd]
      exact Fan.IsLimit.fac hprod (groupedLegs f g) 3
  · intro T f g m hf hg
    apply Fan.IsLimit.hom_ext hprod
    intro i
    rw [Fan.IsLimit.fac]
    fin_cases i
    · have hh := congrArg (fun k => k ≫ fst (A 0) (A 1)) hf
      change (m ≫ lift (π 0) (π 1)) ≫ fst _ _ = _ at hh
      rw [Category.assoc, CartesianMonoidalCategory.lift_fst] at hh
      exact hh
    · have hh := congrArg (fun k => k ≫ snd (A 0) (A 1)) hf
      change (m ≫ lift (π 0) (π 1)) ≫ snd _ _ = _ at hh
      rw [Category.assoc, CartesianMonoidalCategory.lift_snd] at hh
      exact hh
    · have hh := congrArg (fun k => k ≫ fst (A 2) (A 3)) hg
      change (m ≫ lift (π 2) (π 3)) ≫ fst _ _ = _ at hh
      rw [Category.assoc, CartesianMonoidalCategory.lift_fst] at hh
      exact hh
    · have hh := congrArg (fun k => k ≫ snd (A 2) (A 3)) hg
      change (m ≫ lift (π 2) (π 3)) ≫ snd _ _ = _ at hh
      rw [Category.assoc, CartesianMonoidalCategory.lift_snd] at hh
      exact hh

theorem fourProduct_cup_ne_zero (B : Fin 4 → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : ∀ i, P.toOver ⟶ (B i).toOver)
    (hprod : IsLimit (Fan.mk P.toOver π))
    (u : ∀ i, (B i).complexCohomology 1) (hu : ∀ i, u i ≠ 0) :
    SurfaceConstructionQ.CM.fourCup P (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i) (u i)) ≠ 0 := by
  let B01 := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety (B 0) (B 1)
  let B23 := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety (B 2) (B 3)
  let c01 : B01.complexCohomology 2 :=
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace B01.toOver) 1 1
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (fst (B 0).toOver (B 1).toOver) (u 0))
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (snd (B 0).toOver (B 1).toOver) (u 1))
  let c23 : B23.complexCohomology 2 :=
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace B23.toOver) 1 1
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (fst (B 2).toOver (B 3).toOver) (u 2))
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (snd (B 2).toOver (B 3).toOver) (u 3))
  have h01 : c01 ≠ 0 := Kunneth.CM.SurfaceConstruction.complex_exteriorCup_ne_zero
    (Z := B01.presentation) _ _ (tensorProductIsBinaryProduct _ _) 1 1 _ _ (hu 0) (hu 1)
  have h23 : c23 ≠ 0 := Kunneth.CM.SurfaceConstruction.complex_exteriorCup_ne_zero
    (Z := B23.presentation) _ _ (tensorProductIsBinaryProduct _ _) 1 1 _ _ (hu 2) (hu 3)
  have ht := Kunneth.CM.SurfaceConstruction.complex_exteriorCup_ne_zero
    (X := B01.presentation) (Y := B23.presentation) (Z := P.presentation)
    (firstPairMap π) (lastPairMap π) (fourProduct_isBinaryProduct π hprod) 2 2 c01 c23 h01 h23
  have hfirst : Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 2 (firstPairMap π) c01 =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 0) (u 0))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 1) (u 1)) := by
    change Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 2 (firstPairMap π)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace B01.toOver) 1 1 _ _) = _
    erw [SurfaceConstructionQ.CM.schemePullback_cup (X := B01) (firstPairMap π) 1 1,
      SurfaceConstructionQ.CM.schemePullback_comp, SurfaceConstructionQ.CM.schemePullback_comp]
    unfold firstPairMap
    erw [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  have hlast : Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 2 (lastPairMap π) c23 =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 2) (u 2))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 3) (u 3)) := by
    change Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 2 (lastPairMap π)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace B23.toOver) 1 1 _ _) = _
    erw [SurfaceConstructionQ.CM.schemePullback_cup (X := B23) (lastPairMap π) 1 1,
      SurfaceConstructionQ.CM.schemePullback_comp, SurfaceConstructionQ.CM.schemePullback_comp]
    unfold lastPairMap
    erw [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  erw [hfirst, hlast] at ht
  exact ht

/-- The nonvanishing clause of SurfaceConstruction holds for the exact supplied product
and canonical comparison vectors, independently of the switch relation. -/
theorem canonical_switchTensor_ne_zero
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (hprod : IsLimit (Fan.mk X.toOver π)) :
    SurfaceConstructionQ.CM.fourCup X (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
      ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
        (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
          (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) ≠ 0 := by
  apply fourProduct_cup_ne_zero (fun i => (R i).abelianVariety.variety) X π hprod
  intro i hz
  exact ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector_ne_zero E _
    ((R i).complexComparison.injective (hz.trans (map_zero _).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.FourProduct.CM.SurfaceConstruction
