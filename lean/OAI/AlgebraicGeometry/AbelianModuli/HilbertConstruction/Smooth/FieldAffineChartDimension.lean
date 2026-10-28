import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Field Affine Chart Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldAffineChartDimension

noncomputable section

/-! A smooth morphism of relative dimension g over a field has an actual affine chart at every point whose coordinate algebra is standard smooth of dimension g over that field. The ground-field coefficient map uses the canonical Spec/global-functions isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem smoothField_exists_affine_chart_dimension
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (g : ℕ) [SmoothOfRelativeDimension g p] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      RingHom.IsStandardSmoothOfRelativeDimension g
        ((p.appTop ≫ X.presheaf.map V.leTop.op).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) := by
  obtain ⟨U, _, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := g) (f := p) x
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : p x = y := Subsingleton.elim _ _
    exact hy ▸ e hx
  subst U
  have hzero : (Scheme.ΓSpecIso (.of K)).inv.hom.IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  refine ⟨V, hV, hx, ?_⟩
  have happ : p.appLE ⊤ V e = p.appTop ≫ X.presheaf.map V.leTop.op := rfl
  simpa only [Nat.add_zero, happ] using hstd.comp hzero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldAffineChartDimension
