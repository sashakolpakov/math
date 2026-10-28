import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAffineLocalFrame

/-! # Flat Trace Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTraceBasis

noncomputable section

/-! The affine opens on which a finite flat map has a basis of its constant rank form a topological basis. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

abbrev FiniteFlatTraceOpen {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :=
  {U : X.Opens // IsAffineOpen U ∧
    Nonempty (@Module.Basis (Fin n) Γ(X, U) Γ(Y, f ⁻¹ᵁ U) _ _ (f.app U).hom.toModule)}

theorem finiteFlatTraceOpen_isBasis {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] {n : ℕ} (hn : ∀ x, f.finrank x = n) :
    Opens.IsBasis (Set.range (Subtype.val : FiniteFlatTraceOpen f n → X.Opens)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  obtain ⟨V, hxV, hVU, hV, hb⟩ := FlatAffineLocalFrame.finiteFlat_exists_affineLocalBasis f hn hU x hxU
  exact ⟨V, ⟨⟨V, hV, hb⟩, rfl⟩, hxV, hVU.trans hUW⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTraceBasis
