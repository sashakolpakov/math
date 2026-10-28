import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.HomogenizedTransport

/-! # Ideal Transforms -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Arbitrary controlled ideal transforms and initial boundary labels along an actual prefix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def ControlPrefix.IdealTransforms.Construction.iteratedInitialBoundaryEmbedding : (N : ℕ) → (β : Type) → β ↪ ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β
  | 0, β => Function.Embedding.refl β
  | N + 1, β => (⟨some, Option.some_injective β⟩ : β ↪ Option β).trans
      (iteratedInitialBoundaryEmbedding N (Option β))

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.transformIdeal
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    X.IdealSheafData → ℕ → Y.IdealSheafData := by
  induction P with
  | stop => exact fun L _ => L
  | blowup I hI hb hp hs hbl tail ih => exact fun L c => ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI c) c

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.transformIdeal
    {b c : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J L : X.IdealSheafData} {K M : Y.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix c X f L Y g M}
    (h : Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P Q) : P.transformIdeal L c = M := by
  induction h with
  | stop => rfl
  | blowup I hI hb hc hp hq hs hbl tail ih => exact ih

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.canonicalBoundary_initialLabel
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ (β : Type) (D : β → X.IdealSheafData) (j : β),
      P.canonicalBoundary D (ControlPrefix.IdealTransforms.Construction.iteratedInitialBoundaryEmbedding P.stepCount β j) = P.transformIdeal (D j) 1 := by
  induction P with
  | stop => intro β D j; rfl
  | blowup I hI hb hp hs hbl tail ih =>
      intro β D j
      exact ih (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) (some j)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.boundaryAtLength_initialLabel
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {β : Type} (D : β → X.IdealSheafData) (j : β) (N : ℕ) (hN : P.stepCount = N) :
    P.boundaryAtLength D N hN (ControlPrefix.IdealTransforms.Construction.iteratedInitialBoundaryEmbedding N β j) = P.transformIdeal (D j) 1 := by
  subst N
  exact P.canonicalBoundary_initialLabel β D j

end

end OAI.AlgebraicGeometry.Resolution.Blowups
