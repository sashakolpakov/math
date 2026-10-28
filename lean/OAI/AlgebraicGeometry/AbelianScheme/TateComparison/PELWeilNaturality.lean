import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilNaturality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPicardDualMaps
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPerfectPairing
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralBilinearNaturality

/-! # PEL Weil Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELWeilNaturality

noncomputable section

/-! The original PEL Poincare and polarization equations give the
actual integral and rational Weil Tate similitudes and Rosati adjoints. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k] {g N : ℕ}
  (P : PEL.PELFamilyData R g N (Spec (.of k)))
  (δ : Fin g → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (q : ℕ) [Fact q.Prime] (hq : Nat.Coprime q (∏ i, δ i))

private instance polarization_group :
    IsMonHom (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom) :=
  P.polarizationMap.preservesGroup

private instance polarization_finite :
    IsFinite (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.finite

private instance polarization_flat :
    Flat (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.flat

private instance polarization_surjective :
    Surjective (show P.abelian.scheme ⟶ (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual).abelian from P.polarizationMap.hom).left :=
  P.polarizationMap.surjective

namespace PELIsogeny
variable {P} (Q : PEL.PELFamilyData R g N (Spec (.of k)))
  (δ' : Fin g → ℕ) (hδ' : Q.polarizationMap.HasPolarizationType δ')
  (hq' : Nat.Coprime q (∏ i, δ' i)) {m : ℕ} (e : PELIsogenies.PELIsogeny P Q m)

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.tateWeil_similitude
    (x y : Add.schemeTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    PELPerfectPairing.pelTateWeilPairing Q δ' hδ' q hq'
        (Add.schemeTateMap P.abelian.scheme _ q e.isogeny.hom x)
        (Add.schemeTateMap P.abelian.scheme _ q e.isogeny.hom y) =
      m • PELPerfectPairing.pelTateWeilPairing P δ hδ q hq x y := by
  unfold PELPerfectPairing.pelTateWeilPairing
  exact WeilNaturality.isogenyTateWeilPairing_similitude Q.abelian.scheme P.abelian.scheme
    (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled Q.dual) (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual)
    Q.polarizationMap.hom P.polarizationMap.hom q _ _ e.isogeny.hom e.dualHom
    e.dualHom_eq_picard m e.polarization x y

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.rationalWeil_similitude
    (x y : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    LinearMap.BilinForm.baseChange ℚ_[q] (PELPerfectPairing.pelTateWeilPairing Q δ' hδ' q hq')
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom x)
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom y) =
      m • LinearMap.BilinForm.baseChange ℚ_[q] (PELPerfectPairing.pelTateWeilPairing P δ hδ q hq) x y :=
  IntegralBilinearNaturality.integralBilinearBaseChange_similitude (GeometricLattice.geometricTateBasis P.abelian q)
    (PELPerfectPairing.pelTateWeilPairing P δ hδ q hq) (PELPerfectPairing.pelTateWeilPairing Q δ' hδ' q hq')
    (Add.schemeTateMap P.abelian.scheme _ q e.isogeny.hom) m
    (e.tateWeil_similitude δ hδ q hq Q δ' hδ' hq') x y

end PELIsogeny

variable (c : R →+* R) (hR : P.IsRosatiCompatible c)

include hR in
theorem pelTateWeilPairing_adjoint (r : R)
    (x y : Add.schemeTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    PELPerfectPairing.pelTateWeilPairing P δ hδ q hq
        (Add.schemeTateMap P.abelian.scheme _ q (End.endSchemeMap P.abelian.scheme (P.action r)) x) y =
      PELPerfectPairing.pelTateWeilPairing P δ hδ q hq x
        (Add.schemeTateMap P.abelian.scheme _ q (End.endSchemeMap P.abelian.scheme (P.action (c r))) y) := by
  obtain ⟨d, hd, hp⟩ := hR r
  unfold PELPerfectPairing.pelTateWeilPairing
  exact WeilNaturality.isogenyTateWeilPairing_adjoint P.abelian.scheme (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual)
    P.polarizationMap.hom q _ (End.endSchemeMap P.abelian.scheme (P.action r))
    (End.endSchemeMap P.abelian.scheme (P.action (c r))) (End.endSchemeMap P.dual.abelian.scheme d)
    (PEL.PELFamilyData.poincareDual_eq_picard P (P.action r) d hd) hp x y

include hR in
theorem pelRationalWeilPairing_adjoint (r : R)
    (x y : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    LinearMap.BilinForm.baseChange ℚ_[q] (PELPerfectPairing.pelTateWeilPairing P δ hδ q hq)
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap P.abelian.scheme (P.action r)) x) y =
      LinearMap.BilinForm.baseChange ℚ_[q] (PELPerfectPairing.pelTateWeilPairing P δ hδ q hq) x
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap P.abelian.scheme (P.action (c r))) y) :=
  IntegralBilinearNaturality.integralBilinearBaseChange_adjoint (GeometricLattice.geometricTateBasis P.abelian q)
    (PELPerfectPairing.pelTateWeilPairing P δ hδ q hq)
    (Add.schemeTateMap P.abelian.scheme _ q (End.endSchemeMap P.abelian.scheme (P.action r)))
    (Add.schemeTateMap P.abelian.scheme _ q (End.endSchemeMap P.abelian.scheme (P.action (c r))))
    (pelTateWeilPairing_adjoint P δ hδ q hq c hR r) x y

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELWeilNaturality
