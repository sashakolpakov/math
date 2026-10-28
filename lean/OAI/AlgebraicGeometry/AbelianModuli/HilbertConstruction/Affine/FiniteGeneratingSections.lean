import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.FiniteGeneratingSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecGlobalSectionIdentities
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.IsoImage

/-! # Finite Generating Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteGeneratingSections

noncomputable section

/-! Finite global sections give finite global generators on any affine scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem affine_exists_finite_generatingSections {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X, ⊤) Γ(M, ⊤)] :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let N := (pushforward X.toSpecΓ).obj M
  have : N.IsQuasicoherent := Quasicoherent.IsoImage.modulePushforward_quasicoherent_of_isIso X.toSpecΓ M
  have : Module.Finite Γ(X, ⊤) (moduleSpecΓFunctor.obj N) :=
    Module.Finite.equiv (SpecGlobalSectionIdentities.moduleSpecΓPushforwardToSpecIso M).symm
  have : Module.Finite Γ(X, ⊤) Γ(N, ⊤) := by
    change Module.Finite Γ(X, ⊤) (moduleSpecΓFunctor.obj N)
    infer_instance
  obtain ⟨G, hG⟩ := Spec.FiniteGeneratingSections.spec_exists_finite_generatingSections N
  let F := restrictFunctor X.toSpecΓ
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F := by
    dsimp [F]
    infer_instance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF (restrictUnitIso X.toSpecΓ).symm
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((restrictFunctorAdjCounitIso X.toSpecΓ).app M) G'
  have : G''.IsFiniteType := ⟨by
    change Finite G.I
    exact hG.finite⟩
  exact ⟨G'', inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteGeneratingSections
