import OAI.NumberTheory.ArithmeticGroups.Lattices.UniformExteriorVector
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.UniformExteriorLine

/-! # Polynomial -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Polynomial.Construction

noncomputable section

section

/-! A finite-dimensional, field-uniform fixed-vector stabilizer
realization for the connected semisimple matrix groups of Lattices. -/

open scoped Classical
open _root_.MvPolynomial

theorem exists_finite_uniform_exterior_vector_stabilizer
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    ∃ d r : ℕ, ∃ p : Fin r → BoundedRepresentation.Construction.BoundedPolynomials k n d,
      ∀ (K : Type) [Field K] [Algebra k K],
        LinearIndependent K (fun i => Lattices.Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (p i)) ∧
        ∀ g : Algebraic.SL n K, g ∈ G.subgroup K (algebraMap k K) ↔
          exteriorPower.map r (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g).toLinearMap
            (exteriorPower.ιMulti K r (fun i => Lattices.Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (p i))) =
              exteriorPower.ιMulti K r (fun i => Lattices.Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (p i)) := by
  obtain ⟨d, r, p, hp, hvec⟩ := UniformExteriorVector.Construction.exists_uniform_exterior_vector_stabilizer G hconn hsemi
  let q : Fin r → BoundedRepresentation.Construction.BoundedPolynomials k n d := fun i =>
    ⟨p i, (mem_restrictTotalDegree _ _ _).mpr (hp i)⟩
  refine ⟨d, r, q, fun K _ _ => ?_⟩
  obtain ⟨hlin, hg⟩ := hvec K
  let f := (BoundedRepresentation.Construction.BoundedPolynomials K n d).subtype
  let qK : Fin r → BoundedRepresentation.Construction.BoundedPolynomials K n d := fun i => Lattices.Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (q i)
  refine ⟨LinearIndependent.of_comp f hlin, fun g => ?_⟩
  rw [hg g, exteriorPower.map_apply_ιMulti]
  have he := Lattices.Finite.UniformExteriorLine.Construction.exterior_line_equality_iff_injective_map f Subtype.val_injective
    (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g ∘ qK) qK (1 : K)
  have hleft : f ∘ (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g ∘ qK) =
      (fun i => PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K)
        (MvPolynomial.map (algebraMap k K) (p i))) := rfl
  have hright : f ∘ qK = (fun i => MvPolynomial.map (algebraMap k K) (p i)) := rfl
  rw [hleft, hright] at he
  simpa only [one_smul, LinearEquiv.coe_coe] using he

end

section

/-! Right translation over an integral coefficient ring, and its
compatibility with the bounded-degree representation over a field. -/

open scoped Classical
open _root_.MvPolynomial

def rightTranslationOverRing {R : Type} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    Algebraic.CoordinatePolynomial n R →ₐ[R] Algebraic.CoordinatePolynomial n R :=
  MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ l, X (ij.1, l) * C (A l ij.2))

theorem rightTranslationOverRing_coefficient_map
    {R k : Type} [CommRing R] [Field k] {n : ℕ} (ι : R →+* k)
    (A : Matrix (Fin n) (Fin n) R) (p : Algebraic.CoordinatePolynomial n R) :
    MvPolynomial.map ι (rightTranslationOverRing A p) =
      PolynomialAction.Construction.rightTranslate (A.map ι) (MvPolynomial.map ι p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [rightTranslationOverRing]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      simp only [map_mul, hp]
      congr 1
      simp [rightTranslationOverRing, PolynomialAction.Construction.rightTranslate_X]

theorem coefficient_map_totalDegree_eq
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (ι : R →+* S) (hι : Function.Injective ι) (p : MvPolynomial σ R) :
    (MvPolynomial.map ι p).totalDegree = p.totalDegree := by
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective p hι]

theorem rightTranslationOverRing_totalDegree_le
    {R k : Type} [CommRing R] [Field k] {n : ℕ}
    (ι : R →+* k) (hι : Function.Injective ι)
    (A : Matrix (Fin n) (Fin n) R) (p : Algebraic.CoordinatePolynomial n R) :
    (rightTranslationOverRing A p).totalDegree ≤ p.totalDegree := by
  rw [← coefficient_map_totalDegree_eq ι hι (rightTranslationOverRing A p),
    rightTranslationOverRing_coefficient_map]
  exact (PolynomialAction.Construction.rightTranslate_totalDegree_le _ _).trans (UniformPolynomialStabilizer.Construction.coefficient_map_totalDegree_le ι p)

def boundedIntegralCoefficientMap
    {R k : Type} [CommRing R] [Field k] [Algebra R k] (n d : ℕ) :
    restrictTotalDegree (Fin n × Fin n) R d →ₗ[R] BoundedRepresentation.Construction.BoundedPolynomials k n d where
  toFun p := ⟨MvPolynomial.map (algebraMap R k) p.val,
    (mem_restrictTotalDegree _ _ _).mpr ((UniformPolynomialStabilizer.Construction.coefficient_map_totalDegree_le _ _).trans
      ((mem_restrictTotalDegree _ _ _).mp p.property))⟩
  map_add' p q := Subtype.ext (map_add _ p.val q.val)
  map_smul' c p := by
    apply Subtype.ext
    exact (MvPolynomial.mapAlgHom (Algebra.ofId R k)).toLinearMap.map_smul c p.val

def boundedIntegralPolynomialLattice
    {R k : Type} [CommRing R] [Field k] [Algebra R k] (n d : ℕ) :
    Submodule R (BoundedRepresentation.Construction.BoundedPolynomials k n d) := (boundedIntegralCoefficientMap (R := R) (k := k) n d).range

theorem boundedIntegralPolynomialLattice_fg
    {R k : Type} [CommRing R] [Field k] [Algebra R k] (n d : ℕ) :
    (boundedIntegralPolynomialLattice (R := R) (k := k) n d).FG := by
  unfold boundedIntegralPolynomialLattice
  have hfg : (⊤ : Submodule R (restrictTotalDegree (Fin n × Fin n) R d)).FG := Module.Finite.fg_top
  simpa only [Submodule.map_top] using hfg.map (boundedIntegralCoefficientMap (R := R) (k := k) n d)

theorem boundedIntegralPolynomialLattice_full
    {R k : Type} [CommRing R] [Field k] [Algebra R k] (n d : ℕ) :
    Submodule.span k (boundedIntegralPolynomialLattice (R := R) (k := k) n d : Set (BoundedRepresentation.Construction.BoundedPolynomials k n d)) = ⊤ := by
  let s : Set ((Fin n × Fin n) →₀ ℕ) := {m | m.sum (fun _ e => e) ≤ d}
  let b : Module.Basis s k (BoundedRepresentation.Construction.BoundedPolynomials k n d) := MvPolynomial.basisRestrictSupport k s
  have hb (A : Type) [CommRing A] (m : s) :
      ((MvPolynomial.basisRestrictSupport A s) m).val = (monomial m.val 1 : MvPolynomial (Fin n × Fin n) A) := by
    change AddMonoidAlgebra.ofCoeff
      (((Finsupp.supportedEquivFinsupp (R := A) s).symm (Finsupp.single m 1)).val) = _
    rw [Finsupp.supportedEquivFinsupp_symm_single]
    rfl
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨m, rfl⟩
  apply Submodule.subset_span
  refine ⟨MvPolynomial.basisRestrictSupport R s m, ?_⟩
  apply Subtype.ext
  change MvPolynomial.map (algebraMap R k) ((MvPolynomial.basisRestrictSupport R s m).val) =
    (MvPolynomial.basisRestrictSupport k s m).val
  rw [hb, hb]
  simp

end

/-! Integral special-linear matrices preserve the full bounded-degree
polynomial lattice. -/

open scoped Classical
open _root_.MvPolynomial

theorem boundedIntegralPolynomialLattice_action_mem
    {R k : Type} [CommRing R] [Field k] [Algebra R k] [FaithfulSMul R k] {n d : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) R) {p : BoundedRepresentation.Construction.BoundedPolynomials k n d}
    (hp : p ∈ boundedIntegralPolynomialLattice (R := R) (k := k) n d) :
    BoundedRepresentation.Construction.boundedPolynomialRepresentation d (Matrix.SpecialLinearGroup.map (algebraMap R k) g) p ∈
      boundedIntegralPolynomialLattice (R := R) (k := k) n d := by
  obtain ⟨q, rfl⟩ := hp
  let q' : restrictTotalDegree (Fin n × Fin n) R d :=
    ⟨rightTranslationOverRing (g : Matrix (Fin n) (Fin n) R) q.val,
      (mem_restrictTotalDegree _ _ _).mpr
        ((rightTranslationOverRing_totalDegree_le (algebraMap R k)
          (FaithfulSMul.algebraMap_injective R k) _ _).trans
            ((mem_restrictTotalDegree _ _ _).mp q.property))⟩
  refine ⟨q', ?_⟩
  apply Subtype.ext
  exact rightTranslationOverRing_coefficient_map (algebraMap R k)
    (g : Matrix (Fin n) (Fin n) R) q.val

theorem boundedIntegralPolynomialLattice_action_iff
    {R k : Type} [CommRing R] [Field k] [Algebra R k] [FaithfulSMul R k] {n d : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) R) (p : BoundedRepresentation.Construction.BoundedPolynomials k n d) :
    BoundedRepresentation.Construction.boundedPolynomialRepresentation d (Matrix.SpecialLinearGroup.map (algebraMap R k) g) p ∈
        boundedIntegralPolynomialLattice (R := R) (k := k) n d ↔
      p ∈ boundedIntegralPolynomialLattice (R := R) (k := k) n d := by
  constructor
  · intro hp
    have h := boundedIntegralPolynomialLattice_action_mem g⁻¹ hp
    have he : BoundedRepresentation.Construction.boundedPolynomialRepresentation d (Matrix.SpecialLinearGroup.map (algebraMap R k) g⁻¹)
        (BoundedRepresentation.Construction.boundedPolynomialRepresentation d (Matrix.SpecialLinearGroup.map (algebraMap R k) g) p) = p := by
      rw [← LinearEquiv.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
      rfl
    rwa [he] at h
  · exact boundedIntegralPolynomialLattice_action_mem g

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Polynomial.Construction
