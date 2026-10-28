import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ResidualUpdate
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.SequenceCompatibility
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Identities
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceHypersurface

/-! # Control Boundary Endpoint -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

section

/-! Canonical endpoint boundaries and exact total-transform exponents of global control sequences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def MonomialSequence.Construction.SmoothFixedControlSequence.endpointLabels {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (β : Type) : Type :=
  match T with
  | @MonomialSequence.Construction.SmoothFixedControlSequence.terminal _ _ _ _ _ _ => β
  | @MonomialSequence.Construction.SmoothFixedControlSequence.blowup _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.endpointLabels (Option β)

instance MonomialSequence.Construction.SmoothFixedControlSequence.endpointLabels_fintype {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (β : Type) [Fintype β] :
    Fintype (T.endpointLabels β) := by
  induction T generalizing β with
  | terminal => exact inferInstanceAs (Fintype β)
  | blowup I hI hb hp hs hbl tail ih => exact ih (Option β)

def MonomialSequence.Construction.SmoothFixedControlSequence.endpointBoundary {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β : Type}
    (D : β → X.IdealSheafData) : T.endpointLabels β → T.endpoint.IdealSheafData :=
  match T with
  | @MonomialSequence.Construction.SmoothFixedControlSequence.terminal _ _ _ _ _ _ => D
  | @MonomialSequence.Construction.SmoothFixedControlSequence.blowup _ _ _ _ _ _ I hI _ _ _ _ tail =>
      tail.endpointBoundary (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)

def MonomialSequence.Construction.SmoothFixedControlSequence.totalBoundaryExponents {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (a : β → ℕ) : T.endpointLabels β → ℕ :=
  match T with
  | @MonomialSequence.Construction.SmoothFixedControlSequence.terminal _ _ _ _ _ _ => a
  | @MonomialSequence.Construction.SmoothFixedControlSequence.blowup _ _ _ _ _ _ I hI _ _ _ _ tail =>
      tail.totalBoundaryExponents (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents (AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D) a b 0)

theorem MonomialSequence.Construction.SmoothFixedControlSequence.endpointBoundary_nonzero
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β : Type}
    (D : β → X.IdealSheafData) (hD : ∀ l, D l ≠ ⊥) : ∀ l, T.endpointBoundary D l ≠ ⊥ := by
  induction T generalizing β with
  | terminal => exact hD
  | blowup I hI hb hp hs hbl tail ih =>
      exact ih (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_ne_bot I hI D hD)

theorem MonomialSequence.Construction.SmoothFixedControlSequence.endpointBoundary_atlas
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hB : T.boundaryCompatible β D) :
    Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (T.toBase ≫ f) (T.endpointBoundary D) [Finset.univ]) := by
  induction T generalizing β with
  | @terminal Y g hs J ht =>
      change Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (𝟙 Y ≫ g) D [Finset.univ])
      rw [Category.id_comp]
      exact hB
  | @blowup Y hY hN g J I hI hb hp hs hbl tail ih =>
      have h := ih (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) hB.2
      change Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas ((tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ g)
        (tail.endpointBoundary (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)) [Finset.univ])
      rw [Category.assoc]
      exact h

theorem MonomialSequence.Construction.SmoothFixedControlSequence.totalTransform_eq_boundaryMonomial_mul_terminalIdeal
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (a : β → ℕ)
    (hcenters : T.integralCenters) (hB : T.boundaryCompatible β D) :
    (MixedBoundary.Construction.boundaryMonomialSheaf D a * J).comap T.toBase =
      MixedBoundary.Construction.boundaryMonomialSheaf (T.endpointBoundary D) (T.totalBoundaryExponents D a) * T.terminalIdeal := by
  induction T generalizing β with
  | terminal => exact Scheme.IdealSheafData.comap_id _
  | @blowup Y hY hN g J I hI hb hp hs hbl tail ih =>
      let : IsIntegral I.subscheme := hcenters.1
      obtain ⟨A⟩ := hB.1
      have hM : MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ (0 - b) := by
        rw [Nat.zero_sub, pow_zero, Scheme.IdealSheafData.one_eq_top]
        exact le_top
      have he := A.residual_product_integral_center J hI a b 0 hM hp
      rw [GlobalControlled.Identities.Construction.globalBlowupControlledIdeal_zero] at he
      change (MixedBoundary.Construction.boundaryMonomialSheaf D a * J).comap (tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) = _
      rw [Scheme.IdealSheafData.comap_comp, he]
      exact ih (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents (AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D) a b 0) hcenters.2 hB.2

theorem MonomialSequence.Construction.SmoothFixedControlSequence.totalTransform_eq_boundaryMonomial_control_one
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence 1 X f J) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hcenters : T.integralCenters) (hB : T.boundaryCompatible β D) :
    J.comap T.toBase = MixedBoundary.Construction.boundaryMonomialSheaf (T.endpointBoundary D) (T.totalBoundaryExponents D (fun _ => 0)) := by
  have h := T.totalTransform_eq_boundaryMonomial_mul_terminalIdeal D (fun _ => 0) hcenters hB
  have hM : MixedBoundary.Construction.boundaryMonomialSheaf D (fun _ => 0) = 1 := by
    simp only [MixedBoundary.Construction.boundaryMonomialSheaf, pow_zero, Finset.prod_const_one]
  simpa only [hM, one_mul, T.terminalIdeal_eq_top_control_one, ← Scheme.IdealSheafData.one_eq_top, mul_one] using h

end

/-! Original boundary labels retain their exact control-one transforms at every sequence endpoint. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def MonomialSequence.Construction.SmoothFixedControlSequence.initialLabelEmbedding {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) (β : Type) : β ↪ T.endpointLabels β :=
  match T with
  | @MonomialSequence.Construction.SmoothFixedControlSequence.terminal _ _ _ _ _ _ => Function.Embedding.refl β
  | @MonomialSequence.Construction.SmoothFixedControlSequence.blowup _ _ _ _ _ _ _ _ _ _ _ _ tail =>
      (⟨some, Option.some_injective β⟩ : β ↪ Option β).trans (tail.initialLabelEmbedding (Option β))

theorem MonomialSequence.Construction.SmoothFixedControlSequence.endpointBoundary_initialLabel
    {b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b X f J) {β : Type} (D : β → X.IdealSheafData) (j : β) :
    T.endpointBoundary D (T.initialLabelEmbedding β j) = T.transformIdeal (D j) 1 := by
  induction T generalizing β with
  | terminal => rfl
  | @blowup Y hY hN g J I hI hb hp hs hbl tail ih =>
      exact ih (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) (some j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
