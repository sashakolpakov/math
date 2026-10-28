import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELWeilNaturality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitFrameTransport

/-! # PEL Weil Adjoint Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! A PEL family isomorphism transports the actual Weil adjoint
identity by its proved isometry and equivariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k] {g N q : ℕ} [Fact q.Prime]
  {P Q : PEL.PELFamilyData R g N (Spec (.of k))}
  (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
  (hQ : Q.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))
  (e : PELModuli.PELFamilyIso P Q) (c : R →+* R) (hR : Q.IsRosatiCompatible c)

theorem PELModuli.PELFamilyIso.rationalWeil_isometry
    (x y : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    LinearMap.BilinForm.baseChange ℚ_[q] (PELPerfectPairing.pelTateWeilPairing Q δ hQ q hq)
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.abelian.hom x)
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.abelian.hom y) =
      LinearMap.BilinForm.baseChange ℚ_[q] (PELPerfectPairing.pelTateWeilPairing P δ hP q hq) x y := by
  have hi := e.toIsogeny.rationalWeil_similitude δ hP q hq Q δ hQ hq x y
  rw [one_nsmul] at hi
  exact hi

omit [CharZero k] [IsAlgClosed k] in
theorem PELModuli.PELFamilyIso.rationalWeil_map_action (r : R)
    (x : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.abelian.hom
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap P.abelian.scheme (P.action r)) x) =
      Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
        (End.endSchemeMap Q.abelian.scheme (Q.action r))
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.abelian.hom x) := by
  have h : Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (End.endSchemeMap P.abelian.scheme (P.action r) ≫ e.abelian.hom) =
    Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (e.abelian.hom ≫ End.endSchemeMap Q.abelian.scheme (Q.action r)) := by
    congr 1
    exact e.equivariant r
  simp only [Functor.rationalTateMap_comp] at h
  exact LinearMap.congr_fun h x

include hQ e hR in
theorem PELModuli.PELFamilyIso.rationalWeil_adjoint (r : R)
    (x y : Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    LinearMap.BilinForm.baseChange ℚ_[q] (PELPerfectPairing.pelTateWeilPairing P δ hP q hq)
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap P.abelian.scheme (P.action r)) x) y =
      LinearMap.BilinForm.baseChange ℚ_[q] (PELPerfectPairing.pelTateWeilPairing P δ hP q hq) x
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap P.abelian.scheme (P.action (c r))) y) := by
  have hi := e.rationalWeil_isometry δ hP hQ hq
  rw [← hi, ← hi, e.rationalWeil_map_action, e.rationalWeil_map_action]
  exact PELWeilNaturality.pelRationalWeilPairing_adjoint Q δ hQ q hq c hR r _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
