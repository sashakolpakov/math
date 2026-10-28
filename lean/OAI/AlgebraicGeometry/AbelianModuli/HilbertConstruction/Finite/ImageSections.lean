import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Image Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageSections

noncomputable section

/-! Finite morphisms preserve finite generation of affine-open sections of finite-type quasicoherent sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem finite_directImage_affine_sections_finite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : Y.affineOpens) :
    Module.Finite Γ(Y, U.1) Γ((pushforward f).obj M, U.1) := by
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M V
  let : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.app U.1).hom.toAlgebra
  let : Module Γ(Y, U.1) Γ(M, V.1) := Module.compHom Γ(M, V.1) (f.app U.1).hom
  let : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(M, V.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite Γ(Y, U.1) Γ(X, V.1) := f.finite_app U.1 U.2
  have hfinite : Module.Finite Γ(Y, U.1) Γ(M, V.1) :=
    Module.Finite.trans Γ(X, V.1) Γ(M, V.1)
  exact hfinite

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageSections
