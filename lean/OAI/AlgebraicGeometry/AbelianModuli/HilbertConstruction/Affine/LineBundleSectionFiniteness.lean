import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Line Bundle Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual line bundles have finite type, and their sections on every affine open are finite over that open's ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)

theorem Line.Bundles.LineBundle.isFiniteType : L.sheaf.IsFiniteType := by
  refine { exists_localGeneratorsData := ⟨L.localPresentationData.localGeneratorsData, ?_⟩ }
  constructor
  intro x
  exact (L.localPresentationData_isFinite.isFinite_presentation x).isFiniteType_generators

theorem Line.Bundles.LineBundle.affineOpen_sections_finite (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(L.sheaf, U.1) := by
  have := L.isQuasicoherent
  have := L.isFiniteType
  exact Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite L.sheaf U

theorem Line.Bundles.LineBundle.affine_sections_finite [IsAffine X] : Module.Finite Γ(X, ⊤) Γ(L.sheaf, ⊤) :=
  L.affineOpen_sections_finite ⟨⊤, isAffineOpen_top X⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
