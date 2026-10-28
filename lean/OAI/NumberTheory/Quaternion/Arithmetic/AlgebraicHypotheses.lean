import OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

/-! # Algebraic Hypotheses -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicHypotheses

noncomputable section

/-! Algebraic hypotheses for Arithmetic, expressed through polynomial matrix groups.
The definitions concern algebraic groups, not topological simple connectivity.
No approximation assertion is included in any hypothesis. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

variable {F : Type} [Field F] {m n : ℕ}

/-- Scalar extension of the actual defining equations. -/
def baseChange (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) {K : Type} [Field K]
    (f : F →+* K) : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n where
  equations := MvPolynomial.map f '' G.equations
  subgroup L _ ι := G.subgroup L (ι.comp f)
  mem_iff L _ ι g := by
    rw [G.mem_iff]
    simp only [Set.forall_mem_image, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, MvPolynomial.eval₂Hom_map_hom]

/-- A regular group homomorphism represented by polynomial matrix coordinates
over the base field, uniformly over extension fields. -/
structure PolynomialHom (H : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F m)
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) where
  hom : (K : Type) → [Field K] → (ι : F →+* K) → (H.Points ι →* G.Points ι)
  coordinates : Fin n → Fin n → ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial m F
  coordinate_eq : ∀ (K : Type) [Field K] (ι : F →+* K)
    (h : H.Points ι) (i j : Fin n),
    (hom K ι h).val i j = ArithmeticGroups.Lattices.Algebraic.evaluateMatrix ι h.val (coordinates i j)

namespace PolynomialHom

variable {H : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F m} {G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n}

abbrev rational (f : PolynomialHom H G) : H.RationalPoints →* G.RationalPoints :=
  f.hom F (RingHom.id F)

/-- Compatibility with extension of scalars follows from the polynomial coordinates. -/
theorem map_hom (f : PolynomialHom H G) {K L : Type} [Field K] [Field L]
    (ι : F →+* K) (φ : K →+* L) (h : H.Points ι) :
    G.map ι φ (f.hom K ι h) = f.hom L (φ.comp ι) (H.map ι φ h) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup.map_entry, f.coordinate_eq, f.coordinate_eq]
  simp only [ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, MvPolynomial.map_eval₂Hom,
    ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup.map_entry]

/-- Over an algebraically closed characteristic-zero field this is a
surjective algebraic homomorphism with finite central kernel. -/
def IsCentralIsogeny (f : PolynomialHom H G) : Prop :=
  Function.Surjective f.rational ∧
    Finite f.rational.ker ∧ f.rational.ker ≤ Subgroup.center H.RationalPoints

end PolynomialHom

/-- Geometric simple connectivity, tested after scalar extension to the
algebraic closure. In characteristic zero a central isogeny with trivial
kernel is an isomorphism. -/
def IsAlgebraicallySimplyConnected (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) : Prop :=
  ∀ (H : ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup (AlgebraicClosure F))
    (f : PolynomialHom H.matrixGroup (baseChange G (algebraMap F (AlgebraicClosure F)))),
    f.IsCentralIsogeny → Function.Injective f.rational

/-- Noncommutative, geometrically connected, and without a proper nontrivial
connected closed normal subgroup over the algebraic closure. -/
def IsAbsolutelyAlmostSimple (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) : Prop :=
  letI : TopologicalSpace G.GeometricPoints := G.geometricTopology
  G.IsGeometricallyConnected ∧
    (∃ a b : G.GeometricPoints, a * b ≠ b * a) ∧
    ∀ N : Subgroup G.GeometricPoints,
      N.Normal → IsClosed (N : Set G.GeometricPoints) →
      IsConnected (N : Set G.GeometricPoints) → N = ⊥ ∨ N = ⊤

end

end OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicHypotheses
