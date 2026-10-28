import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyConnectingScalars
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteHomologySequence

/-! # Cohomology Exact Finiteness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyExactFiniteness

noncomputable section

/-! Finiteness of actual base-linear sheaf cohomology is stable under
short exact sequences. No affine cover or projective presentation is used. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteHomologySequence
universe u

/-- Finiteness in all degrees for the canonical base-ring action. -/
def BaseCohomologyFinite {X B : Scheme.{u}} (f : X ⟶ B) (M : X.Modules) : Prop :=
  ∀ n : ℕ, letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
    Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H M n)

namespace BaseCohomologyFinite
variable {X B : Scheme.{u}} (f : X ⟶ B) [IsNoetherianRing Γ(B, ⊤)]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS

theorem middle (h₁ : BaseCohomologyFinite f S.X₁)
    (h₃ : BaseCohomologyFinite f S.X₃) : BaseCohomologyFinite f S.X₂ := by
  intro n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₁ n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₂ n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₃ n
  have : Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H S.X₁ n) := h₁ n
  have : Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H S.X₃ n) := h₃ n
  apply SheafCohomology.Projective.FiniteHomologySequence.finite_of_exact (CohomologyConnectingScalars.baseCohomologyLinearMap f n S.f)
    (CohomologyConnectingScalars.baseCohomologyLinearMap f n S.g)
  intro x
  constructor
  · exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_exact₂_explicit
      (hS.map_of_exact (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X)) n x
  · rintro ⟨y, rfl⟩
    exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_comp_zero₂
      (S := S.map (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X)) n y

theorem right (h₁ : BaseCohomologyFinite f S.X₁)
    (h₂ : BaseCohomologyFinite f S.X₂) : BaseCohomologyFinite f S.X₃ := by
  intro n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₂ n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₃ n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₁ (n + 1)
  have : Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H S.X₂ n) := h₂ n
  have : Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H S.X₁ (n + 1)) := h₁ (n + 1)
  apply SheafCohomology.Projective.FiniteHomologySequence.finite_of_exact (CohomologyConnectingScalars.baseCohomologyLinearMap f n S.g)
    (CohomologyConnectingScalars.baseCohomologyConnectingLinearMap f hS n)
  intro x
  constructor
  · exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_exact₃_explicit
      (hS.map_of_exact (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X)) n (n + 1) rfl x
  · rintro ⟨y, rfl⟩
    exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_comp_zero₃
      (hS.map_of_exact (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X)) n (n + 1) rfl y

theorem left (h₂ : BaseCohomologyFinite f S.X₂)
    (h₃ : BaseCohomologyFinite f S.X₃) : BaseCohomologyFinite f S.X₁ := by
  intro n
  cases n with
  | zero =>
      let := hS.mono_f
      let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₁ 0
      let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₂ 0
      have : Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H S.X₂ 0) := h₂ 0
      have hmono : Mono ((SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)).map S.f) :=
        inferInstance
      apply Module.Finite.of_injective (CohomologyConnectingScalars.baseCohomologyLinearMap f 0 S.f)
      intro x y hxy
      apply (SheafCohomology.AffineH.Projective.hZeroEquivGlobalSections S.X₁).injective
      apply (ModuleCat.mono_iff_injective (S.f.val.app (.op ⊤))).mp
        hmono
      change S.f.app ⊤ (SheafCohomology.AffineH.Projective.hZeroEquivGlobalSections S.X₁ x) =
        S.f.app ⊤ (SheafCohomology.AffineH.Projective.hZeroEquivGlobalSections S.X₁ y)
      rw [SheafCohomology.AffineH.Projective.hZeroEquivGlobalSections_naturality, SheafCohomology.AffineH.Projective.hZeroEquivGlobalSections_naturality]
      exact congrArg (SheafCohomology.AffineH.Projective.hZeroEquivGlobalSections S.X₂) hxy
  | succ n =>
      let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₃ n
      let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₁ (n + 1)
      let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f S.X₂ (n + 1)
      have : Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H S.X₃ n) := h₃ n
      have : Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H S.X₂ (n + 1)) := h₂ (n + 1)
      apply SheafCohomology.Projective.FiniteHomologySequence.finite_of_exact (CohomologyConnectingScalars.baseCohomologyConnectingLinearMap f hS n)
        (CohomologyConnectingScalars.baseCohomologyLinearMap f (n + 1) S.f)
      intro x
      constructor
      · exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_exact₁_explicit
          (hS.map_of_exact (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X)) n (n + 1) rfl x
      · rintro ⟨y, rfl⟩
        exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_comp_zero₁
          (hS.map_of_exact (SheafCohomology.Module.ProjectiveAffine.ModuleSheaf.toSheaf X)) n (n + 1) rfl y

end BaseCohomologyFinite

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyExactFiniteness
