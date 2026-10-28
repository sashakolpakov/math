import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineSectionExact

/-! # Base Global Sections Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalSectionsExact

noncomputable section

/-! Exactness and cokernels of actual global sections when the first cohomology vanishes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)

def baseGlobalSectionsMap {M N : X.Modules} (f : M ⟶ N) :
    letI := BaseZeroSections.baseGlobalSectionsModule π M
    letI := BaseZeroSections.baseGlobalSectionsModule π N
    Γ(M, ⊤) →ₗ[Γ(S, ⊤)] Γ(N, ⊤) := by
  letI := BaseZeroSections.baseGlobalSectionsModule π M
  letI := BaseZeroSections.baseGlobalSectionsModule π N
  exact { (f.val.app (op ⊤)).hom.toAddMonoidHom with
    map_smul' := fun r x => (f.val.app (op ⊤)).hom.map_smul (π.appTop r) x }

theorem globalSections_exact_of_shortExact {T : ShortComplex X.Modules} (hT : T.ShortExact) :
    Function.Exact (T.f.app ⊤) (T.g.app ⊤) := by
  let F := Module.ProjectiveAffine.ModuleSheaf.toSheaf X
  have hF : (T.map F).ShortExact := hT.map_of_exact F
  intro x
  constructor
  · intro hx
    exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_equiv₀_exact₂ hF
      (isTerminalTop : IsTerminal (⊤ : X.Opens)) x hx
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : T.X₁ ⟶ T.X₃ => f.app ⊤ y) T.zero
    exact h

theorem globalSections_surjective_of_HOne_vanish {T : ShortComplex X.Modules}
    (hT : T.ShortExact) [Subsingleton (AffineH.Projective.H T.X₁ 1)] :
    Function.Surjective (T.g.app ⊤) := by
  let F := Module.ProjectiveAffine.ModuleSheaf.toSheaf X
  have hF : (T.map F).ShortExact := hT.map_of_exact F
  have : Subsingleton (CategoryTheory.Sheaf.H (T.map F).X₁ 1) :=
    inferInstanceAs (Subsingleton (AffineH.Projective.H T.X₁ 1))
  exact SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H hF
    (isTerminalTop : IsTerminal (⊤ : X.Opens))

def globalSectionsCokernelEquiv {T : ShortComplex X.Modules}
    (hT : T.ShortExact) [Subsingleton (AffineH.Projective.H T.X₁ 1)] :
    letI := BaseZeroSections.baseGlobalSectionsModule π T.X₁
    letI := BaseZeroSections.baseGlobalSectionsModule π T.X₂
    letI := BaseZeroSections.baseGlobalSectionsModule π T.X₃
    (Γ(T.X₂, ⊤) ⧸ (baseGlobalSectionsMap π T.f).range) ≃ₗ[Γ(S, ⊤)] Γ(T.X₃, ⊤) := by
  letI := BaseZeroSections.baseGlobalSectionsModule π T.X₁
  letI := BaseZeroSections.baseGlobalSectionsModule π T.X₂
  letI := BaseZeroSections.baseGlobalSectionsModule π T.X₃
  let f := baseGlobalSectionsMap π T.f
  let g := baseGlobalSectionsMap π T.g
  have hex : Function.Exact f g := globalSections_exact_of_shortExact hT
  have heq : f.range = g.ker := (LinearMap.exact_iff.mp hex).symm
  exact (Submodule.quotEquivOfEq _ _ heq).trans
    (g.quotKerEquivOfSurjective (globalSections_surjective_of_HOne_vanish hT))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalSectionsExact
