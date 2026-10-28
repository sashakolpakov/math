import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GeometricTheta
import OAI.RepresentationTheory.Theta.Geometric.Active.Cartan

/-! # Canonical Active Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv.Local

noncomputable section

/-! The raw-basis clause of the full GeometricTheta output uniquely determines its
active algebra equivalence. Thus subsequent restrictions use the actual
canonical inclusion, without identifying independent choices by fiat. -/

theorem activeHeckeEquiv_eq_of_raw_matching
    (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)
    (basis : AbelianScheme.TateComparison.Local.LocalType s → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s)
    (hbasis : ∀ t, AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s)
      (AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t))
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q v)
    (he : ∀ a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight, ∃ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeSLRepresentative q a) T ∧
      RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q v e T = basis (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeType v a)) :
    e = RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v := by
  choose T hT hmatch using he
  have hcanonical (a : RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.ActiveWeight) :
      RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q v (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v) (T a) =
        basis (RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.activeType v a) := by
    obtain ⟨S, hS, hSmap⟩ := RepresentationTheory.Theta.Geometric.Active.Basis.Spherical.active_basis_matching q v basis hbasis a
    rw [AbelianScheme.TateComparison.HeckeKernel.rawDoubleCoset_unique _ (hT a) hS]
    exact hSmap
  have hlinear : e.toLinearMap = (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v).toLinearMap := by
    apply LinearMap.ext_on (RepresentationTheory.Theta.Geometric.Active.Cartan.Spherical.active_raw_span q T hT)
    rintro _ ⟨a, rfl⟩
    apply Subtype.ext
    exact (hmatch a).trans (hcanonical a).symm
  apply AlgEquiv.ext
  exact LinearMap.congr_fun hlinear

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv.Local
