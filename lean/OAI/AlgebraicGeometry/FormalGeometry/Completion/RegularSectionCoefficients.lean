import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.CoefficientLinear
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularLinearCombination
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Regular Section Coefficients -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularSectionCoefficients

noncomputable section

/-! A globally generated line bundle admits a global section whose
coefficients act injectively on a coherent module in any finite family of affine frames. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u v

theorem exists_global_section_regular_on_affine_frames
    {X : Scheme.{u}} [IsLocallyNoetherian X] [Infinite Γ(X, ⊤)]
    (hfield : IsField Γ(X, ⊤)) (P : X.Modules) (hP : Frame.SectionDetection.Construction.HasFrameSections P)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    {ι : Type v} [Finite ι] (U : ι → X.affineOpens)
    (e : ∀ i, P.over (U i).1 ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i).1)) :
    ∃ s : Γ(P, ⊤), ∀ i, Function.Injective
      (fun x : Γ(M, (U i).1) => Frame.CoefficientLinear.Construction.frameCoefficientLinear P (U i).1 (e i) s • x) := by
  let : Field Γ(X, ⊤) := hfield.toField
  let (i : ι) : Algebra Γ(X, ⊤) Γ(X, (U i).1) := Frame.CoefficientLinear.Construction.openSectionsAlgebra X (U i).1
  have (i : ι) : IsNoetherianRing Γ(X, (U i).1) :=
    IsLocallyNoetherian.component_noetherian (U i)
  have (i : ι) : Module.Finite Γ(X, (U i).1) Γ(M, (U i).1) :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M (U i)
  apply RegularLinearCombination.Construction.exists_simultaneous_regular_linear_combination
    (fun i => Γ(X, (U i).1)) (fun i => Γ(M, (U i).1))
    (fun i => Frame.CoefficientLinear.Construction.frameCoefficientLinear P (U i).1 (e i))
  intro i p hp
  exact Frame.CoefficientLinear.Construction.frameCoefficientLinear_avoids_prime hP (U i).1 (U i).2 (e i) ⟨p, hp.isPrime⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularSectionCoefficients
