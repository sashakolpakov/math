import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateRepresentation

/-! # Coordinate Integral Vector -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIntegralVector.Construction

noncomputable section

/-! An integral fixed vector and its full invariant lattice in a common
finite coordinate space over every extension field. -/

open scoped Classical

def integralExteriorCoordinateLattice
    {R k : Type} [CommRing R] [Field k] [Algebra R k] (n d r : ℕ) :
    Submodule R (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k) :=
  (ExteriorLattice.Construction.exteriorLatticeSpan (k := k) (Integral.Polynomial.Construction.boundedIntegralPolynomialLattice (R := R) n d) r).map
    ((ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r).toLinearMap.restrictScalars R)

theorem integralExteriorCoordinateLattice_fg
    {R k : Type} [CommRing R] [Field k] [Algebra R k] (n d r : ℕ) :
    (integralExteriorCoordinateLattice (R := R) (k := k) n d r).FG :=
  (ExteriorLattice.Construction.exteriorLatticeSpan_fg _ (Integral.Polynomial.Construction.boundedIntegralPolynomialLattice_fg n d) r).map _

theorem integralExteriorCoordinateLattice_full
    {R k : Type} [CommRing R] [Field k] [Algebra R k] (n d r : ℕ) :
    Submodule.span k (integralExteriorCoordinateLattice (R := R) (k := k) n d r :
      Set (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k)) = ⊤ := by
  let Ω := ExteriorLattice.Construction.exteriorLatticeSpan (k := k) (Integral.Polynomial.Construction.boundedIntegralPolynomialLattice (R := R) (k := k) n d) r
  let e := ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r
  have hfull : Submodule.span k (Ω : Set (⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d))) = ⊤ :=
    ExteriorLattice.Construction.exteriorLatticeSpan_full _ (Integral.Polynomial.Construction.boundedIntegralPolynomialLattice_full n d) r
  change Submodule.span k (Ω.map (e.toLinearMap.restrictScalars R) :
    Set (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k)) = ⊤
  rw [Submodule.map_coe]
  change Submodule.span k (e.toLinearMap ''
    (Ω : Set (⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)))) = ⊤
  rw [← Submodule.map_span, hfull, Submodule.map_top]
  exact e.range

theorem integralExteriorCoordinateLattice_action_mem
    {R k : Type} [CommRing R] [Field k] [Algebra R k] [FaithfulSMul R k] {n d r : ℕ}
    (A : Matrix.SpecialLinearGroup (Fin n) R) {x : ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k}
    (hx : x ∈ integralExteriorCoordinateLattice (R := R) n d r) :
    CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r (Matrix.SpecialLinearGroup.map (algebraMap R k) A) x ∈
      integralExteriorCoordinateLattice (R := R) n d r := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨ExteriorRepresentation.Construction.boundedExteriorRepresentation d r (Matrix.SpecialLinearGroup.map (algebraMap R k) A) w,
    Integral.ExteriorVector.Construction.integral_exterior_lattice_action_mem A hw, ?_⟩
  exact (CoordinateRepresentation.Construction.boundedExteriorCoordinates_action _ w).symm

theorem exists_integral_coordinate_vector_stabilizer
    {R k : Type} [CommRing R] [IsDomain R] [Field k] [CharZero k]
    [Algebra R k] [IsFractionRing R k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    ∃ d r : ℕ, ∃ x : ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k,
      x ∈ integralExteriorCoordinateLattice (R := R) n d r ∧
      ∀ (K : Type) [Field K] [Algebra k K],
        (fun i => algebraMap k K (x i)) ≠ 0 ∧
        ∀ g : Algebraic.SL n K, g ∈ G.subgroup K (algebraMap k K) ↔
          CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r g (fun i => algebraMap k K (x i)) =
            (fun i => algebraMap k K (x i)) := by
  obtain ⟨d, r, p, c, _, hw, hfixed⟩ :=
    Integral.ExteriorVector.Construction.exists_integral_uniform_exterior_vector_stabilizer (R := R) G hconn hsemi
  let w := c • exteriorPower.ιMulti k r p
  let x := ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r w
  refine ⟨d, r, x, ⟨w, hw, rfl⟩, fun K _ _ => ?_⟩
  let wK := algebraMap k K c • exteriorPower.ιMulti K r
    (fun i => Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (p i))
  have he : ExteriorCoordinates.Construction.boundedExteriorCoordinates K n d r wK = (fun i => algebraMap k K (x i)) := by
    ext s
    change (ExteriorCoordinates.Construction.boundedExteriorCoordinates K n d r wK) s =
      algebraMap k K (ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r w s)
    dsimp only [wK, w]
    rw [map_smul, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul,
      ExteriorCoordinates.Construction.boundedExteriorCoordinates_wedge_coefficient_map]
  refine ⟨?_, fun g => ?_⟩
  · rw [← he]
    exact fun h => (hfixed K).1 ((ExteriorCoordinates.Construction.boundedExteriorCoordinates K n d r).injective
      (h.trans (map_zero (ExteriorCoordinates.Construction.boundedExteriorCoordinates K n d r)).symm))
  · rw [← he, CoordinateRepresentation.Construction.boundedExteriorCoordinates_action,
      (ExteriorCoordinates.Construction.boundedExteriorCoordinates K n d r).injective.eq_iff]
    exact (hfixed K).2 g

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIntegralVector.Construction
