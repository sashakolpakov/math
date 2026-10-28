import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PositivePeriods
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalClass

/-! # Theta Construction Cubical Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ThetaConstructionCubicalPolarization

noncomputable section

/-! The original ThetaConstruction theta construction retains the cubical identity
of the same primitive ample bundle whose Chern matrix is prescribed.
No tensor multiple or additional polarization assumption is introduced. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral OAI.AlgebraicGeometry.Picard.ThetaConstruction.PositivePeriods.Geometric OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalClass

theorem e36PolarizationFactor_cubical {g : ℕ} {E : Picard.ThetaConstruction.DefinitionsIntegral.IntegralMatrix g}
    (T : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g E) (hE : E.transpose = -E) :
    (T.polarizationFactor hE).IsCubical := by
  intro l m n w z u
  exact RepresentationTheory.Theta.Geometric.Cubical.Automorphy.polarizationAutomorphy_cube T.riemannForm (Picard.ThetaConstruction.DefinitionsIntegral.Geometric.integralLatticeBasis T)
    (Picard.ThetaConstruction.DefinitionsIntegral.Geometric.integralLatticeForm T) T.lattice.subtype (Picard.ThetaConstruction.DefinitionsIntegral.Geometric.integralLatticeForm_isAlt T hE)
    T.hermitian (Picard.ThetaConstruction.DefinitionsIntegral.Geometric.integralLatticeForm_riemann T) l m n w z u

theorem e36AlgebraicModel_ample_cubical_pairing {g : ℕ} {E : Picard.ThetaConstruction.DefinitionsIntegral.IntegralMatrix g}
    {T : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g E} (hE : E.transpose = -E) (M : Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel T) :
    ∃ L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left, L.IsAmple ∧
      RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 ∧
      ∀ l m : T.lattice, Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (Picard.ThetaConstruction.DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ) := by
  obtain ⟨U, V, f, g, _, hdeg, hUi, hVi, hUd, hVd, _, _, hf, hg, _, hamp⟩ :=
    M.exists_ample_theta_quotient (hP := hE)
  exact ⟨RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left, hamp,
    RepresentationTheory.Theta.Geometric.Intrinsic.CubicalClass.native_cubical_theta_quotient_class U V (e36PolarizationFactor_cubical T hE)
      hUi hVi hUd hVd M.abelian M.period M.period_add f g hf hg,
    M.nativeThetaChernForm_integral U V f g hf hg hdeg⟩

theorem e36AlgebraicPositivePeriod_cubical {g : ℕ}
    (E : Picard.ThetaConstruction.DefinitionsIntegral.IntegralMatrix g) (hE : E.transpose = -E)
    (P : Submodule ℂ (Picard.ThetaConstruction.DefinitionsIntegral.CVec g)) (hP : Picard.ThetaConstruction.DefinitionsIntegral.CompatiblePositivePeriod E P) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
      (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Picard.ThetaConstruction.DefinitionsIntegral.Index g) A),
      Picard.ThetaConstruction.IntrinsicPolarization.Geometric.PreservesPolarizationMatrix A L hL b E ∧ (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker = P ∧
        RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect A (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 := by
  obtain ⟨T, hT⟩ := Picard.ThetaConstruction.DefinitionsIntegral.realize_positive_period E hE P hP
  obtain ⟨M⟩ := Picard.ThetaConstruction.PeriodModel.Geometric.exists_algebraicPeriodModel T
  obtain ⟨L, hL, hcube, hpair⟩ := e36AlgebraicModel_ample_cubical_pairing hE M
  exact ⟨M.abelian, L, hL, M.markedNativeBasis,
    M.markedNativeBasis_polarization L hL hpair, M.markedNativeBasis_kernel.trans hT, hcube⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ThetaConstructionCubicalPolarization
