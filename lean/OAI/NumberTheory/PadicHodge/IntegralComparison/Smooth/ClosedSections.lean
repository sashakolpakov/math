import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSubopen
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedSections

noncomputable section

/-! Smoothness of a closed subscheme gives smoothness of its actual
affine section quotient over the original affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y S : Scheme.{u}} [IsAffine S]

abbrev algebra (π : Y ⟶ S) (U : Y.Opens) : Algebra Γ(S, ⊤) Γ(Y, U) :=
  (π.appLE ⊤ U le_top).hom.toAlgebra

theorem smooth_sections (π : Y ⟶ S) [Smooth π] (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := algebra π U
    Algebra.Smooth Γ(S, ⊤) Γ(Y, U) := by
  let := algebra π U
  exact RingHom.smooth_algebraMap.mp (π.smooth_appLE (isAffineOpen_top S) hU le_top)

variable (f : X ⟶ Y) [IsClosedImmersion f] (π : Y ⟶ S) (U : Y.Opens)

def sectionMap :
    letI := algebra π U
    letI := algebra (f ≫ π) (f ⁻¹ᵁ U)
    Γ(Y, U) →ₐ[Γ(S, ⊤)] Γ(X, f ⁻¹ᵁ U) := by
  letI := algebra π U
  letI := algebra (f ≫ π) (f ⁻¹ᵁ U)
  exact
    { __ := (f.app U).hom
      commutes' r := by
        have h := Scheme.Hom.appLE_comp_appLE f π ⊤ U (f ⁻¹ᵁ U) le_top le_rfl
        rw [Scheme.Hom.appLE_eq_app] at h
        exact ConcreteCategory.congr_hom h r }

def quotientEquiv (hU : IsAffineOpen U) :
    letI := algebra π U
    letI := algebra (f ≫ π) (f ⁻¹ᵁ U)
    (Γ(Y, U) ⧸ f.ker.ideal ⟨U, hU⟩) ≃ₐ[Γ(S, ⊤)] Γ(X, f ⁻¹ᵁ U) := by
  letI := algebra π U
  letI := algebra (f ≫ π) (f ⁻¹ᵁ U)
  exact (Ideal.quotientEquivAlgOfEq Γ(S, ⊤) (f.ker_apply ⟨U, hU⟩)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := sectionMap f π U) (f.app_surjective U hU))

theorem smooth_quotient [Smooth (f ≫ π)] (hU : IsAffineOpen U) :
    letI := algebra π U
    Algebra.Smooth Γ(S, ⊤) (Γ(Y, U) ⧸ f.ker.ideal ⟨U, hU⟩) := by
  let := algebra π U
  let := algebra (f ≫ π) (f ⁻¹ᵁ U)
  have := smooth_sections (f ≫ π) (f ⁻¹ᵁ U) (hU.preimage f)
  exact Algebra.Smooth.of_equiv (quotientEquiv f π U hU).symm

include π in
theorem exists_regular_subopen [Smooth π] [Smooth (f ≫ π)]
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(Y, U)]
    (p : PrimeSpectrum Γ(Y, U)) (hp : f.ker.ideal ⟨U, hU⟩ ≤ p.asIdeal) :
    ∃ (V : Y.Opens) (_hV : IsAffineOpen V), V ≤ U ∧ hU.fromSpec p ∈ V ∧
      ∃ rs : List Γ(Y, V), RingHom.ker (f.app V).hom = Ideal.ofList rs ∧
        RingTheory.Sequence.IsRegular Γ(Y, V) rs := by
  let := algebra π U
  have := smooth_sections π U hU
  have := smooth_quotient f π U hU
  obtain ⟨V, hV, hVU, hpV, rs, hI, hreg⟩ :=
    RegularSubopen.exists_regular_subopen (k := Γ(S, ⊤)) f.ker U hU p hp
  exact ⟨V, hV, hVU, hpV, rs, (f.ker_apply ⟨V, hV⟩).symm.trans hI, hreg⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedSections
