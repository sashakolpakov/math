import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeGeometricPointLift
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Isogeny Type Base Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyTypeBaseDescent

noncomputable section

/-! The finite-flat degree and the actual geometric kernel type of an
isogeny descend through a surjective base morphism locally of finite type. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem isogenyType_of_baseChange {S T : Scheme.{u}} {g : ℕ}
    {A D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D)
    (b : T ⟶ S) [Surjective b] [LocallyOfFiniteType b] {δ : Fin g → ℕ}
    (h : (p.pullback b).HasPolarizationType δ) : p.HasPolarizationType δ := by
  refine ⟨?_, ?_⟩
  · intro d
    obtain ⟨d', rfl⟩ := (pullback.fst D.scheme.hom b).surjective d
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ (Specialization.base_change_square b p.hom) d').symm.trans
      (h.degree d')
  · intro K _ _ s
    obtain ⟨t, ht⟩ := Finite.TypeGeometricPointLift.exists_geometric_point_lift b s
    subst s
    exact ⟨(p.kernelBaseChangeEquiv b (Over.mk t)).symm.trans (h.geometricKernel K t).some⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyTypeBaseDescent
