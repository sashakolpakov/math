import OAI.RepresentationTheory.Theta.Geometric.PeriodPolarizationAutomorphy

/-! # Automorphy -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original polarization factor has the exact cubical identity.
Both products of theta factors on the triple period space therefore have
the same automorphy factor, before any algebraic comparison is made. -/

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

theorem Cubical.Automorphy.poincareAutomorphy_first_add (l m n w z u : V) :
    Dual.PeriodProjectivity.poincareAutomorphy H (l + m) n (w + z) u =
      Dual.PeriodProjectivity.poincareAutomorphy H l n w u * Dual.PeriodProjectivity.poincareAutomorphy H m n z u := by
  simp only [Dual.PeriodProjectivity.poincareAutomorphy, map_add, LinearMap.add_apply]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem Cubical.Automorphy.poincareAutomorphy_second_add (l m n w z u : V) :
    Dual.PeriodProjectivity.poincareAutomorphy H l (m + n) w (z + u) =
      Dual.PeriodProjectivity.poincareAutomorphy H l m w z * Dual.PeriodProjectivity.poincareAutomorphy H l n w u := by
  simp only [Dual.PeriodProjectivity.poincareAutomorphy, map_add, LinearMap.add_apply]
  rw [← Complex.exp_add]
  congr 1
  ring

variable {L I : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
    (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L) (e : L →+ V)

theorem Cubical.Automorphy.polarizationAutomorphy_cube (hB : B.IsAlt)
    (hsym : ∀ u v, H v u = star (H u v))
    (hint : ∀ l m, (H (e l) (e m)).im = (B l m : ℝ))
    (l m n : L) (w z u : V) :
    PolarizationAutomorphy.polarizationAutomorphy b B e H (l + m + n) (w + z + u) *
        PolarizationAutomorphy.polarizationAutomorphy b B e H l w * PolarizationAutomorphy.polarizationAutomorphy b B e H m z *
        PolarizationAutomorphy.polarizationAutomorphy b B e H n u =
      PolarizationAutomorphy.polarizationAutomorphy b B e H (l + m) (w + z) *
        PolarizationAutomorphy.polarizationAutomorphy b B e H (l + n) (w + u) *
        PolarizationAutomorphy.polarizationAutomorphy b B e H (m + n) (z + u) := by
  simp only [PolarizationAutomorphy.polarizationAutomorphy_poincare b B e H hB hsym hint, map_add,
    Cubical.Automorphy.poincareAutomorphy_first_add]
  ring

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.periodPolarizationAutomorphy_cube (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (l m n : D.pel.reference.lattice) (w z u : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.periodPolarizationAutomorphy hg x (l + m + n) (w + z + u) *
        D.periodPolarizationAutomorphy hg x l w * D.periodPolarizationAutomorphy hg x m z *
        D.periodPolarizationAutomorphy hg x n u =
      D.periodPolarizationAutomorphy hg x (l + m) (w + z) *
        D.periodPolarizationAutomorphy hg x (l + n) (w + u) *
        D.periodPolarizationAutomorphy hg x (m + n) (z + u) :=
  Cubical.Automorphy.polarizationAutomorphy_cube (D.periodHermitian hg x) (D.referenceBasis hg)
    D.pel.reference.integralForm (D.referenceLatticePeriodEmbedding x)
    (D.referenceIntegralForm_isAlt hg) (D.periodHermitian_hermitian hg x)
    (D.periodHermitian_integral_embedding hg x) l m n w z u

end

end OAI.RepresentationTheory.Theta.Geometric
