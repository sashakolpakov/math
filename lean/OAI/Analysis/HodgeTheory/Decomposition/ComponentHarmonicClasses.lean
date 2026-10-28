import OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonic
import OAI.Analysis.HodgeTheory.Decomposition.SmoothHarmonic

/-! # Component Harmonic Classes -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonicClasses.Constructions

noncomputable section

section

/-! Genuine harmonic component families represent every Betti class
uniquely, through the existing closed-form comparison map. -/

theorem closedFormBettiClass_eq_iff_exact (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (a b : X.componentClosedForms n) :
    X.closedFormBettiClass n a = X.closedFormBettiClass n b ↔ a.val - b.val ∈ X.componentExactForms n := by
  change X.deRhamBettiEquiv n (X.componentDeRhamClass n a) =
    X.deRhamBettiEquiv n (X.componentDeRhamClass n b) ↔ _
  rw [(X.deRhamBettiEquiv n).injective.eq_iff, X.componentDeRhamClass_eq_iff]

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  [∀ C : irreducibleComponents X.carrier, MeasurableSpace (X.componentVariety C).analyticSpace]
  [∀ C : irreducibleComponents X.carrier, BorelSpace (X.componentVariety C).analyticSpace] (n : ℕ)

theorem componentHarmonics_closed (a : ComponentHarmonicTypes.Constructions.ComponentHarmonics X n) : a.val ∈ X.componentClosedForms (n + 1) := by
  rw [X.mem_componentClosedForms_iff]
  intro C
  exact ((AdjointAlgebra.Constructions.projectivePositiveLaplacian_eq_zero_iff (X.componentVariety C) n (a.val C)).mp (congrFun a.property C)).1

def componentHarmonicToClosed : ComponentHarmonicTypes.Constructions.ComponentHarmonics X n →ₗ[ℂ] X.componentClosedForms (n + 1) :=
  (ComponentHarmonicTypes.Constructions.ComponentHarmonics X n).subtype.codRestrict _ (componentHarmonics_closed X n)

def componentHarmonicBettiClass : ComponentHarmonicTypes.Constructions.ComponentHarmonics X n →ₗ[ℂ] X.complexCohomology (n + 1) :=
  (X.closedFormBettiClass (n + 1)).comp (componentHarmonicToClosed X n)

def componentClosedHarmonicPart (a : X.componentClosedForms (n + 1)) : ComponentHarmonicTypes.Constructions.ComponentHarmonics X n :=
  ⟨ComponentHarmonic.Constructions.componentSmoothHarmonicPart X n a.val, ComponentHarmonic.Constructions.componentSmoothHarmonicPart_harmonic X n a.val⟩

theorem component_closed_harmonic_remainder_exact (a : X.componentClosedForms (n + 1)) :
    a.val - (componentClosedHarmonicPart X n a).val ∈ X.componentExactForms (n + 1) := by
  rw [X.mem_componentExactForms_iff]
  intro C
  have ha := (X.mem_componentClosedForms_iff (n + 1) a.val).mp a.property C
  let V := X.componentVariety C
  refine ⟨AdjointAlgebra.Constructions.projectiveCodifferential V n (SmoothHarmonic.Constructions.projectiveSmoothGreen V n (a.val C)), ?_⟩
  change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AdjointAlgebra.Constructions.projectiveCodifferential V n (SmoothHarmonic.Constructions.projectiveSmoothGreen V n (a.val C))) =
    a.val C - SmoothHarmonic.Constructions.projectiveSmoothHarmonicPart V n (a.val C)
  have h := SmoothHarmonic.Constructions.projective_closed_harmonic_representative V n (a.val C) ha
  conv_rhs => lhs; rw [h]
  abel

theorem componentClosedHarmonicPart_class (a : X.componentClosedForms (n + 1)) :
    componentHarmonicBettiClass X n (componentClosedHarmonicPart X n a) = X.closedFormBettiClass (n + 1) a := by
  symm
  apply (closedFormBettiClass_eq_iff_exact X (n + 1) a (componentHarmonicToClosed X n (componentClosedHarmonicPart X n a))).mpr
  exact component_closed_harmonic_remainder_exact X n a

theorem componentHarmonicBettiClass_surjective : Function.Surjective (componentHarmonicBettiClass X n) := by
  intro c
  obtain ⟨a, rfl⟩ := Core.Constructions.closedFormBettiClass_surjective X (n + 1) c
  exact ⟨componentClosedHarmonicPart X n a, componentClosedHarmonicPart_class X n a⟩

theorem componentHarmonicBettiClass_injective : Function.Injective (componentHarmonicBettiClass X n) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro a ha
  change X.closedFormBettiClass (n + 1) (componentHarmonicToClosed X n a) = 0 at ha
  have hc : X.closedFormBettiClass (n + 1) (componentHarmonicToClosed X n a) =
      X.closedFormBettiClass (n + 1) 0 := by simpa only [map_zero] using ha
  have he := (closedFormBettiClass_eq_iff_exact X (n + 1) _ _).mp hc
  change a.val - 0 ∈ X.componentExactForms (n + 1) at he
  rw [sub_zero, X.mem_componentExactForms_iff] at he
  apply Subtype.ext
  funext C
  obtain ⟨b, hb⟩ := he C
  have hδ := ((AdjointAlgebra.Constructions.projectivePositiveLaplacian_eq_zero_iff (X.componentVariety C) n (a.val C)).mp (congrFun a.property C)).2
  exact AdjointAlgebra.Constructions.exact_coclosed_eq_zero (X.componentVariety C) n (a.val C) b hb hδ

def componentHarmonicBettiEquiv : ComponentHarmonicTypes.Constructions.ComponentHarmonics X n ≃ₗ[ℂ] X.complexCohomology (n + 1) :=
  LinearEquiv.ofBijective (componentHarmonicBettiClass X n)
    ⟨componentHarmonicBettiClass_injective X n, componentHarmonicBettiClass_surjective X n⟩

end

/-! The prescribed Betti Hodge pieces are the images of the independent
pure harmonic families under the actual de Rham comparison isomorphism. -/

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  [∀ C : irreducibleComponents X.carrier, MeasurableSpace (X.componentVariety C).analyticSpace]
  [∀ C : irreducibleComponents X.carrier, BorelSpace (X.componentVariety C).analyticSpace] (n : ℕ)

theorem hodgePiece_eq_harmonic_image (i : Core.Constructions.Bidegree (n + 1)) :
    Core.Constructions.hodgePiece X (n + 1) i =
      (ComponentHarmonicTypes.Constructions.componentHarmonicType X n i).map (componentHarmonicBettiClass X n) := by
  rw [Core.Constructions.hodgePiece_eq_image]
  apply le_antisymm
  · rintro c ⟨a, ha, rfl⟩
    refine ⟨componentClosedHarmonicPart X n a, ?_, componentClosedHarmonicPart_class X n a⟩
    exact ComponentHarmonic.Constructions.componentSmoothHarmonicPart_pure X n i a.val ha
  · rintro c ⟨a, ha, rfl⟩
    exact ⟨componentHarmonicToClosed X n a, ha, rfl⟩

theorem componentHarmonicType_iSupIndep : iSupIndep (ComponentHarmonicTypes.Constructions.componentHarmonicType X n) := by
  let H := ComponentHarmonicTypes.Constructions.ComponentHarmonics X n
  have hi : iSupIndep (fun i : Core.Constructions.Bidegree (n + 1) => H ⊓ Core.Constructions.pureFormsAt X (n + 1) i) :=
    (Types.Constructions.pureFormsAt_iSupIndep X (n + 1)).mono (fun _ => inf_le_right)
  rw [← iSupIndep_map_orderIso_iff H.mapIic]
  apply iSupIndep.of_coe_Iic_comp
  change iSupIndep (fun i => ((Core.Constructions.pureFormsAt X (n + 1) i).comap H.subtype).map H.subtype)
  simpa only [Submodule.map_comap_subtype] using hi

theorem componentHarmonicType_span : (⨆ i, ComponentHarmonicTypes.Constructions.componentHarmonicType X n i) = ⊤ := by
  apply top_unique
  intro a _
  rw [← ComponentHarmonicTypes.Constructions.sum_componentHarmonicProjection X n a]
  apply Submodule.sum_mem
  intro i _
  exact (le_iSup (ComponentHarmonicTypes.Constructions.componentHarmonicType X n) i) (ComponentHarmonicTypes.Constructions.componentHarmonicProjection_pure X n i a)

theorem hodgePiece_iSupIndep_positive : iSupIndep (Core.Constructions.hodgePiece X (n + 1)) := by
  have hi := (componentHarmonicType_iSupIndep X n).map_orderIso
    (Submodule.orderIsoMapComap (componentHarmonicBettiEquiv X n))
  change iSupIndep (fun i => (ComponentHarmonicTypes.Constructions.componentHarmonicType X n i).map (componentHarmonicBettiClass X n)) at hi
  simpa only [← hodgePiece_eq_harmonic_image] using hi

theorem hodgePiece_span_positive : (⨆ i, Core.Constructions.hodgePiece X (n + 1) i) = ⊤ := by
  simp_rw [hodgePiece_eq_harmonic_image]
  rw [← Submodule.map_iSup, componentHarmonicType_span, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (componentHarmonicBettiClass_surjective X n)

theorem hodge_decomposition_positive : DirectSum.IsInternal (Core.Constructions.hodgePiece X (n + 1)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (hodgePiece_iSupIndep_positive X n) (hodgePiece_span_positive X n)

end

end OAI.Analysis.HodgeTheory.Decomposition.ComponentHarmonicClasses.Constructions
