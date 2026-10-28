import Mathlib

/-! # Algebraic -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

noncomputable section

/-!
Concrete affine matrix groups for Lattices. A group is presented as the common
zero set of polynomials inside SL(n), over every extension field. Thus its
point groups and scalar-extension maps are fixed by equations, not by an
uninterpreted arithmetic predicate. Working in SL loses no connected
semisimple linear algebraic groups in characteristic zero: every character,
including the determinant of a faithful representation, is trivial.

Geometric connectedness and semisimplicity use the actual Zariski topology
over an algebraic closure. Semisimplicity means that every connected closed
normal solvable subgroup is trivial. Cocharacters are uniformly polynomial
in t and t⁻¹ over all extension fields. None of these definitions assumes
discreteness, covolume, or compactness of an arithmetic quotient.
-/

open scoped Classical

abbrev SL (n : ℕ) (K : Type) [CommRing K] :=
  Matrix.SpecialLinearGroup (Fin n) K

abbrev CoordinatePolynomial (n : ℕ) (k : Type) [CommRing k] :=
  MvPolynomial (Fin n × Fin n) k

def evaluateMatrix {n : ℕ} {k K : Type} [CommRing k] [CommRing K]
    (ι : k →+* K) (g : SL n K) : CoordinatePolynomial n k →+* K :=
  MvPolynomial.eval₂Hom ι (fun ij => g ij.1 ij.2)

/-- A reduced affine matrix group, described by equations over k.
The supplied subgroup structures assert only closure under the group laws. -/
structure MatrixAlgebraicGroup (k : Type) [Field k] (n : ℕ) where
  equations : Set (CoordinatePolynomial n k)
  subgroup : (K : Type) → [Field K] → (k →+* K) → Subgroup (SL n K)
  mem_iff : ∀ (K : Type) [Field K] (ι : k →+* K) (g : SL n K),
    g ∈ subgroup K ι ↔ ∀ p ∈ equations, evaluateMatrix ι g p = 0

namespace MatrixAlgebraicGroup

variable {k : Type} [Field k] {n : ℕ} (G : MatrixAlgebraicGroup k n)

abbrev Points {K : Type} [Field K] (ι : k →+* K) := ↥(G.subgroup K ι)

abbrev RationalPoints := G.Points (RingHom.id k)

abbrev GeometricPoints := G.Points (algebraMap k (AlgebraicClosure k))

/-- Scalar extension is the entrywise matrix map. -/
def map {K L : Type} [Field K] [Field L] (ι : k →+* K)
    (f : K →+* L) : G.Points ι →* G.Points (f.comp ι) where
  toFun g := ⟨Matrix.SpecialLinearGroup.map f g.val, by
    apply (G.mem_iff L (f.comp ι) _).mpr
    intro p hp
    have h := congrArg f ((G.mem_iff K ι g.val).mp g.property p hp)
    simpa only [evaluateMatrix, MvPolynomial.map_eval₂Hom, map_zero,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] using h⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ g.val h.val

@[simp] theorem map_entry {K L : Type} [Field K] [Field L]
    (ι : k →+* K) (f : K →+* L) (g : G.Points ι) (i j : Fin n) :
    (G.map ι f g).val i j = f (g.val i j) := rfl

theorem map_injective {K L : Type} [Field K] [Field L]
    (ι : k →+* K) (f : K →+* L) : Function.Injective (G.map ι f) := by
  intro g h he
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply f.injective
  exact congrArg (fun x : G.Points (f.comp ι) => x.val i j) he

/-- The prime ideal associated to a geometric point is its evaluation kernel. -/
def geometricPrime (g : G.GeometricPoints) :
    PrimeSpectrum (CoordinatePolynomial n (AlgebraicClosure k)) :=
  ⟨RingHom.ker (evaluateMatrix (RingHom.id _) g.val), RingHom.ker_isPrime _⟩

/-- The ordinary Zariski topology pulled back from the affine coordinate ring. -/
@[instance_reducible] def geometricTopology : TopologicalSpace G.GeometricPoints :=
  TopologicalSpace.induced G.geometricPrime inferInstance

def IsGeometricallyConnected : Prop :=
  @ConnectedSpace G.GeometricPoints G.geometricTopology

def IsSemisimple : Prop :=
  letI : TopologicalSpace G.GeometricPoints := G.geometricTopology
  ∀ N : Subgroup G.GeometricPoints,
    N.Normal → IsClosed (N : Set G.GeometricPoints) →
    IsConnected (N : Set G.GeometricPoints) → Group.IsSolvable N → N = ⊥

/-- A k-defined algebraic homomorphism G_m → G. Uniform polynomial
coordinates in (t,t⁻¹) encode regularity and scalar-extension compatibility. -/
structure Cocharacter where
  hom : (K : Type) → [Field K] → (ι : k →+* K) → (Kˣ →* G.Points ι)
  coordinates : Fin n → Fin n → MvPolynomial (Fin 2) k
  coordinate_eq : ∀ (K : Type) [Field K] (ι : k →+* K)
    (t : Kˣ) (i j : Fin n),
    (hom K ι t).val i j =
      MvPolynomial.eval₂Hom ι
        (fun a : Fin 2 => if a = 0 then (t : K) else ((t⁻¹ : Kˣ) : K))
        (coordinates i j)

/-- Uniform regular coordinates force compatibility with scalar extension. -/
theorem Cocharacter.map_hom (c : G.Cocharacter)
    {K L : Type} [Field K] [Field L] (ι : k →+* K) (f : K →+* L) (t : Kˣ) :
    G.map ι f (c.hom K ι t) = c.hom L (f.comp ι) (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [map_entry, c.coordinate_eq, c.coordinate_eq, MvPolynomial.map_eval₂Hom]
  apply congrArg (fun x : Fin 2 → L =>
    MvPolynomial.eval₂Hom (f.comp ι) x (c.coordinates i j))
  funext a
  split_ifs <;> rfl

end MatrixAlgebraicGroup

/-- A faithful matrix realization of a connected semisimple k-group. -/
structure ConnectedSemisimpleKGroup (k : Type) [Field k] where
  dimension : ℕ
  matrixGroup : MatrixAlgebraicGroup k dimension
  connected : matrixGroup.IsGeometricallyConnected
  semisimple : matrixGroup.IsSemisimple

/-- k-rank zero: every k-defined cocharacter is trivial. -/
def IsAnisotropic {k : Type} [Field k] (G : ConnectedSemisimpleKGroup k) : Prop :=
  ∀ c : G.matrixGroup.Cocharacter,
    ∀ (K : Type) [Field K] (ι : k →+* K), c.hom K ι = 1

/-- Actual compactness of the group of real points at a specified embedding. -/
def IsCompactAtRealPlace {k : Type} [Field k]
    (G : ConnectedSemisimpleKGroup k) (v : k →+* ℝ) : Prop :=
  CompactSpace (G.matrixGroup.Points v)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic
