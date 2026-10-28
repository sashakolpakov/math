import OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRelativeLine

/-! # Mv Polynomial Retraction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRetraction.Construction

noncomputable section

/-! Retraction neighborhoods of selected coordinate hypersurfaces, preserving the other coordinates. -/

universe u

variable {σ k R : Type u} [Field k] [CommRing R]
  [Algebra (MvPolynomial σ k) R] [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]

attribute [local instance] MvPolynomialRelativeLine.Construction.coordinateLineBaseAlgebra MvPolynomialRelativeLine.Construction.coordinateLineAlgebra
  MvPolynomialRelativeLine.Construction.coordinateLine_scalarTower MvPolynomialRelativeLine.Construction.coordinateLine_originalScalarTower

abbrev coordinateLineFiber (h : σ) := Blowups.Etale.HypersurfaceRetraction.Construction.etaleCoordinateFiber (MvPolynomialRelativeLine.Construction.coordinateLineBase (k := k) h) R

/-- The fiber used by the relative-line construction is the original
selected-coordinate hypersurface as an algebra over the ground field. -/
def coordinateLineFiberEquiv (h : σ) : coordinateLineFiber (k := k) (R := R) h ≃ₐ[k]
    (R ⧸ Ideal.span {algebraMap (MvPolynomial σ k) R (MvPolynomial.X h)}) :=
  Ideal.quotientEquivAlgOfEq k (congrArg (fun z : R => Ideal.span {z}) (MvPolynomialRelativeLine.Construction.coordinateLineMap_X h))

omit [IsScalarTower k (MvPolynomial σ k) R] in
theorem coordinateLineFiberEquiv_mk (h : σ) (x : R) :
    coordinateLineFiberEquiv (k := k) (R := R) h (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk (Ideal.span {algebraMap (MvPolynomial σ k) R (MvPolynomial.X h)}) x :=
  Ideal.quotientEquivAlgOfEq_mk k _ x

variable [Algebra.Etale (MvPolynomial σ k) R]

attribute [local instance] MvPolynomialRelativeLine.Construction.coordinateLine_etale

/-- Every selected étale coordinate hypersurface has an actual étale ambient
refinement retracted onto the same fiber. The ground field, quotient map,
and every other polynomial coordinate are preserved. -/
theorem exists_coordinate_retraction_neighborhood (h : σ) :
    let H := coordinateLineFiber (k := k) (R := R) h
    ∃ (V : Type u) (_ : CommRing V) (_ : Algebra k V) (_ : Algebra H V)
      (_ : Algebra (Polynomial H) V),
      IsScalarTower k H V ∧ IsScalarTower H (Polynomial H) V ∧
      Algebra.Etale (Polynomial H) V ∧
      ∃ g : R →+* V, g.Etale ∧
        (∀ c : k, g (algebraMap k R c) = algebraMap k V c) ∧
        g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X h)) = algebraMap (Polynomial H) V Polynomial.X ∧
        (∀ j : {j : σ // j ≠ h},
          g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) =
            algebraMap H V (Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)))) ∧
        ∃ e : (V ⧸ Ideal.span {algebraMap (Polynomial H) V Polynomial.X}) ≃ₐ[H] H,
          e.toRingHom.comp ((Ideal.Quotient.mk _).comp g) = Ideal.Quotient.mk _ := by
  let A := MvPolynomialRelativeLine.Construction.coordinateLineBase (k := k) h
  let H := coordinateLineFiber (k := k) (R := R) h
  obtain ⟨V, vRing, hAlg, pAlg, ht, he, g, hg, hgX, hgA, ε, hε⟩ :=
    Blowups.Etale.HypersurfaceRetraction.Construction.exists_etale_hypersurface_retraction_neighborhood A R
  let : CommRing V := vRing
  let : Algebra H V := hAlg
  let : Algebra (Polynomial H) V := pAlg
  let : Algebra k V := ((algebraMap H V).comp (algebraMap k H)).toAlgebra
  let : IsScalarTower k H V := IsScalarTower.of_algebraMap_eq' rfl
  have hgk (c : k) : g (algebraMap k R c) = algebraMap k V c := by
    have hc := hgA (MvPolynomial.C c)
    change g (MvPolynomialRelativeLine.Construction.coordinateLineBaseMap h (MvPolynomial.C c)) =
      algebraMap H V (Ideal.Quotient.mk _ (MvPolynomialRelativeLine.Construction.coordinateLineBaseMap h (MvPolynomial.C c))) at hc
    rw [MvPolynomialRelativeLine.Construction.coordinateLineBaseMap_C] at hc
    exact hc
  have hgcoord : g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X h)) =
      algebraMap (Polynomial H) V Polynomial.X := by
    change g (MvPolynomialRelativeLine.Construction.coordinateLineMap h Polynomial.X) = _ at hgX
    rw [MvPolynomialRelativeLine.Construction.coordinateLineMap_X] at hgX
    exact hgX
  have hideal : Ideal.span {algebraMap (Polynomial H) V Polynomial.X} =
      Ideal.span {g (algebraMap (Polynomial A) R Polynomial.X)} :=
    congrArg (fun z : V => Ideal.span {z}) hgX.symm
  let e : (V ⧸ Ideal.span {algebraMap (Polynomial H) V Polynomial.X}) ≃ₐ[H] H :=
    (Ideal.quotientEquivAlgOfEq H hideal).trans ε
  refine ⟨V, vRing, inferInstance, hAlg, pAlg, inferInstance, ht, he, g, hg, hgk, hgcoord, ?_, e, ?_⟩
  · intro j
    have hj := hgA (MvPolynomial.X j)
    change g (MvPolynomialRelativeLine.Construction.coordinateLineBaseMap h (MvPolynomial.X j)) =
      algebraMap H V (Ideal.Quotient.mk _ (MvPolynomialRelativeLine.Construction.coordinateLineBaseMap h (MvPolynomial.X j))) at hj
    rw [MvPolynomialRelativeLine.Construction.coordinateLineBaseMap_X] at hj
    exact hj
  · apply RingHom.ext
    intro x
    change ε (Ideal.quotientEquivAlgOfEq H hideal (Ideal.Quotient.mk _ (g x))) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact RingHom.congr_fun hε x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRetraction.Construction
