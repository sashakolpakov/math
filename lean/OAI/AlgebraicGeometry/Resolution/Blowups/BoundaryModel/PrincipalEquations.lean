import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.EquationCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.TransformRegularElements

/-! # Principal Equations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Equal principal boundary ideals admit the same étale model with adjusted unit factors. -/

theorem BoundaryModel.PrincipalEquations.Construction.regular_principal_equations_unit {R : Type*} [CommRing R] (w v : R) (hw : IsRegular w)
    (he : Ideal.span {w} = Ideal.span {v}) : ∃ u : R, IsUnit u ∧ v = u * w := by
  have hv : v ∈ Ideal.span {w} := he.symm ▸ Ideal.mem_span_singleton_self v
  have hw' : w ∈ Ideal.span {v} := he ▸ Ideal.mem_span_singleton_self w
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hv
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hw'
  have hab : a * b = 1 := by
    apply hw.left
    calc
      w * (a * b) = (w * a) * b := (mul_assoc _ _ _).symm
      _ = v * b := by rw [← ha]
      _ = w * 1 := by rw [← hb, mul_one]
  exact ⟨a, isUnit_iff_exists_inv.mpr ⟨b, hab⟩, ha.trans (mul_comm w a)⟩

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.component_regular
    {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
    {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (j : ι) : IsRegular (w j) := by
  cases hc : M.coordinate j with
  | none =>
      rw [M.equation j, hc, mul_one]
      exact (M.multiplierUnit j).isRegular
  | some s =>
      rw [M.equation j, hc]
      exact (M.multiplierUnit j).isRegular.mul
        (TransformRegularElements.Construction.etale_ringHom_preserves_regular M.map M.etale (MvPolynomial.X s)
          (IsRegular.of_ne_zero (MvPolynomial.X_ne_zero s)))

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.replacePrincipalEquations
    {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
    {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (z : ι → R)
    (hz : ∀ j, Ideal.span {w j} = Ideal.span {z j}) : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι z := by
  choose a ha he using fun j => BoundaryModel.PrincipalEquations.Construction.regular_principal_equations_unit (w j) (z j) (M.component_regular j) (hz j)
  exact (M.mulUnits a ha).congrEquations z he

end

end OAI.AlgebraicGeometry.Resolution.Blowups
