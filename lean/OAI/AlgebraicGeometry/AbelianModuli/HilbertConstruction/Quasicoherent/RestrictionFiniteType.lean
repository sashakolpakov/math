import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections

/-! # Restriction Finite Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType

noncomputable section

/-! Finite-type quasicoherent sheaves remain finite type under open restriction and sheaf isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

theorem quasicoherent_openRestrict_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    (M.restrict f).IsFiniteType := by
  apply HilbertConstruction.Finite.TypeFromAffineSections.module_finiteType_of_affine_sections_finite
  intro U
  have : Module.Finite Γ(Y, f ''ᵁ U.1) Γ(M, f ''ᵁ U.1) :=
    Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  exact Open.RestrictionSectionFiniteness.module_openRestrict_sections_finite f M U.1

theorem quasicoherent_finiteType_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] : N.IsFiniteType := by
  apply HilbertConstruction.Finite.TypeFromAffineSections.module_finiteType_of_affine_sections_finite
  intro U
  have : Module.Finite Γ(X, U.1) Γ(M, U.1) := Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M U
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U.1) := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let eΓ : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(N, U.1) := (F.mapIso e).toLinearEquiv
  exact Module.Finite.equiv eΓ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType
