import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CurveCoefficient
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.RetractionDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.RetractionCoverage

/-! # Surface Order Tree -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SurfaceOrderTree.Construction

noncomputable section

/-! Finite actual order-reduction trees on étale coordinate surfaces. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]

section Coordinates

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
  (R : CommRingCat.{u}) [Algebra k R] [Algebra (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]

/-- A coordinate maximal-contact equation on an actual étale surface
constructs a finite ambient order-reduction tree, including the complement
of the hypersurface and every point on the hypersurface. -/
theorem exists_coordinate_surface_order_tree
    (hd : ringKrullDim R ≤ 2) (J : Ideal R) (n : ℕ) (h : σ)
    (hz : algebraMap (MvPolynomial σ k) R (MvPolynomial.X h) ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Nonempty (Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R J) := by
  let : Algebra.Smooth k (MvPolynomial σ k) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth k R := Algebra.Smooth.comp k (MvPolynomial σ k) R
  let H := MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h
  let : Algebra.Smooth k H := RetractionDimension.Construction.coordinateLineFiber_smooth h
  have hdH : ringKrullDim H ≤ 1 :=
    RetractionDimension.Construction.coordinateLineFiber_dimension_induction h 1 (by simpa using hd)
  obtain ⟨V, cV, akV, aHV, aHPV, hkHV, hHPV, heV, g, hg, hgk, hcoord, _, e, hcomm⟩ :=
    MvPolynomialRetraction.Construction.exists_coordinate_retraction_neighborhood (k := k) (R := R) h
  let f : R →ₐ[k] V := { g with commutes' := hgk }
  let : Algebra.Smooth k V := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k f hg
  have hz' := Ideal.mem_map_of_mem g hz
  rw [Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hg J n, hcoord] at hz'
  obtain ⟨T⟩ := Blowups.Smooth.CurveCoefficient.Construction.exists_retracted_curve_maximal_contact_tree k (.of H) (.of V)
    hdH e (J.map g) n hz'
  have hcover (q : PrimeSpectrum R)
      (hq : algebraMap (MvPolynomial σ k) R (MvPolynomial.X h) ∈ q.asIdeal) :
      ∃ _i : ULift.{u} Unit, ∃ Q : PrimeSpectrum V, PrimeSpectrum.comap g Q = q := by
    obtain ⟨η, hη⟩ := RetractionCoverage.Construction.coordinate_retraction_lifts_hypersurface_point h
      (algebraMap H[X] V X) g e hcomm q.asIdeal hq
    refine ⟨⟨()⟩, ⟨RingHom.ker η, RingHom.ker_isPrime η⟩, PrimeSpectrum.ext ?_⟩
    ext x
    change η (g x) = 0 ↔ x ∈ q.asIdeal
    rw [show η (g x) = algebraMap R q.asIdeal.ResidueField x from RingHom.congr_fun hη x]
    exact Ideal.algebraMap_residueField_eq_zero
  obtain ⟨S, _⟩ := Blowups.Etale.HypersurfaceTreeCover.Construction.exists_control_tree_of_hypersurface_cover k R J
    (algebraMap (MvPolynomial σ k) R (MvPolynomial.X h)) n T.blowupDepth hz
    (ULift.{u} Unit) (fun _ => .of V) (fun _ => f) (fun _ => hg) hcover
    (fun _ => T) (fun _ => le_rfl)
  exact ⟨S⟩

end Coordinates

variable {τ : Type} [Fintype τ] [DecidableEq τ]
  (R : CommRingCat.{u}) [Algebra k R]

/-- Explicit étale coordinate maps with finite small index types give
the same actual surface tree; lifting the indices preserves the ground map
and the chosen hypersurface equation exactly. -/
theorem exists_surface_order_tree_of_coordinate_map
    (ψ : MvPolynomial τ k →+* R) (hψ : ψ.Etale)
    (hcoeff : ∀ c : k, ψ (MvPolynomial.C c) = algebraMap k R c)
    (hd : ringKrullDim R ≤ 2) (J : Ideal R) (n : ℕ) (h : τ)
    (hz : ψ (MvPolynomial.X h) ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Nonempty (Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k (n + 1) R J) := by
  let E := MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} τ ≃ τ)
  let φ := ψ.comp E.toRingHom
  have hφ : φ.Etale := RingHom.Etale.stableUnderComposition E.toRingHom ψ
    (RingHom.Etale.of_bijective E.bijective) hψ
  have hC (c : k) : φ (MvPolynomial.C c) = algebraMap k R c := by
    change ψ (MvPolynomial.rename (Equiv.ulift : ULift.{u} τ ≃ τ) (MvPolynomial.C c)) = _
    rw [MvPolynomial.rename_C, hcoeff]
  let : Algebra (MvPolynomial (ULift.{u} τ) k) R := φ.toAlgebra
  let : IsScalarTower k (MvPolynomial (ULift.{u} τ) k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (hC c).symm)
  let : Algebra.Etale (MvPolynomial (ULift.{u} τ) k) R := RingHom.etale_algebraMap.mp hφ
  apply exists_coordinate_surface_order_tree k R hd J n (ULift.up h)
  change ψ (MvPolynomial.rename (Equiv.ulift : ULift.{u} τ ≃ τ) (MvPolynomial.X (ULift.up h))) ∈ _
  rw [MvPolynomial.rename_X]
  exact hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SurfaceOrderTree.Construction
