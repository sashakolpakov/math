import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.Boundary

/-! # Canonical Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Boundary labels are determined by the number of actual steps, independently of the schemes and ideal presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels : ℕ → Type → Type
  | 0, β => β
  | n + 1, β => iteratedBoundaryLabels n (Option β)

instance ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels_fintype (n : ℕ) (β : Type) [Fintype β] :
    Fintype (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels n β) := by
  induction n generalizing β with
  | zero => exact inferInstanceAs (Fintype β)
  | succ n ih => exact ih (Option β)

variable {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.stepCount_of_followsCenters (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    (centers : List X.IdealSheafData) (hP : P.followsCenters centers) : P.stepCount = centers.length := by
  induction P with
  | stop =>
      change centers = [] at hP
      rw [hP]
      rfl
  | blowup I hI hb hp hs hbl tail ih =>
      obtain ⟨cs, rfl, hcs⟩ := hP
      change tail.stepCount + 1 = cs.length + 1
      have ht := ih _ hcs
      rw [List.length_map] at ht
      rw [ht]

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpointLabelsEquiv (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (β : Type) :
    P.endpointLabels β ≃ ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels P.stepCount β := by
  induction P generalizing β with
  | stop => exact Equiv.refl β
  | blowup I hI hb hp hs hbl tail ih => exact ih (Option β)

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.canonicalBoundary (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) {β : Type}
    (D : β → X.IdealSheafData) : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels P.stepCount β → Y.IdealSheafData :=
  fun l => P.endpointBoundary D ((P.endpointLabelsEquiv β).symm l)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
