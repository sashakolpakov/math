import OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticPlane
import OAI.RepresentationTheory.Weil.UnitarySplitting.TracePairing
import OAI.RepresentationTheory.Weil.UnitarySplitting.Oscillator

/-! # Symplectic Coordinates -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticCoordinates

noncomputable section

/-! Symplectic coordinates by induction on dimension. No existence of
coordinates, Lagrangians, or lifts is assumed. -/

section

open scoped BigOperators

variable {F : Type*} [Field F]

abbrev Coordinates (F : Type*) (d : ℕ) := (Fin d → F) × (Fin d → F)

def coordinatePairing (d : ℕ) (x y : Coordinates F d) : F :=
  ∑ i, (x.2 i * y.1 i - x.1 i * y.2 i)

def prependCoordinates (d : ℕ) :
    ((F × F) × Coordinates F d) ≃ₗ[F] Coordinates F (d + 1) where
  toFun x := (Fin.cons x.1.1 x.2.1, Fin.cons x.1.2 x.2.2)
  invFun x := ((x.1 0, x.2 0), (Fin.tail x.1, Fin.tail x.2))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' a x := by
    apply Prod.ext <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem prependCoordinates_pairing (d : ℕ)
    (x y : (F × F) × Coordinates F d) :
    coordinatePairing (d + 1) (prependCoordinates d x) (prependCoordinates d y) =
      (x.1.2 * y.1.1 - x.1.1 * y.1.2) + coordinatePairing d x.2 y.2 := by
  simp [coordinatePairing, prependCoordinates, Fin.sum_univ_succ]
  ring

theorem exists_coordinates {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (B : LinearMap.BilinForm F V)
    (hAlt : B.IsAlt) (hNondeg : B.Nondegenerate) :
    ∃ (d : ℕ) (e : V ≃ₗ[F] Coordinates F d),
      ∀ x y, B x y = coordinatePairing d (e x) (e y) := by
  classical
  suffices ∀ N, Module.finrank F V = N →
      ∃ (d : ℕ) (e : V ≃ₗ[F] Coordinates F d),
        ∀ x y, B x y = coordinatePairing d (e x) (e y) by
    exact this _ rfl
  intro N hdim
  induction N using Nat.strong_induction_on generalizing V with
  | h N ih =>
    by_cases hsub : Subsingleton V
    · let : Subsingleton V := hsub
      refine ⟨0, LinearEquiv.ofSubsingleton V (Coordinates F 0), ?_⟩
      intro x y
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx, coordinatePairing]
    · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨u, hu⟩ := exists_ne (0 : V)
      obtain ⟨v₀, hv₀⟩ : ∃ v₀, B u v₀ ≠ 0 := by
        by_contra! h
        exact hu (hNondeg.1 u h)
      let v := (B u v₀)⁻¹ • v₀
      have huv : B u v = 1 := by simp [v, hv₀]
      let W := SymplecticPlane.planeComplement B u v
      let ePlane := SymplecticPlane.decomposePlane B hAlt u v huv
      have hdimW : Module.finrank F W < N := by
        have heq := ePlane.finrank_eq
        simp only [Module.finrank_prod, Module.finrank_self] at heq
        change Module.finrank F V = (1 + 1) + Module.finrank F W at heq
        omega
      have hAltW : (B.restrict W).IsAlt := fun x => hAlt x.val
      have hNondegW : (B.restrict W).Nondegenerate :=
        SymplecticPlane.complement_nondegenerate B hAlt hNondeg u v huv
      obtain ⟨d, eW, heW⟩ := ih (Module.finrank F W) hdimW
        (B.restrict W) hAltW hNondegW rfl
      let e : V ≃ₗ[F] Coordinates F (d + 1) := ePlane.trans
        (((LinearEquiv.refl F (F × F)).prodCongr eW).trans (prependCoordinates d))
      refine ⟨d + 1, e, ?_⟩
      intro x y
      have hpair := SymplecticPlane.pairing_decomposition B hAlt u v huv (ePlane x) (ePlane y)
      change B (ePlane.symm (ePlane x)) (ePlane.symm (ePlane y)) = _ at hpair
      rw [ePlane.symm_apply_apply, ePlane.symm_apply_apply] at hpair
      change B x y = coordinatePairing (d + 1)
        (prependCoordinates d ((ePlane x).1, eW (ePlane x).2))
        (prependCoordinates d ((ePlane y).1, eW (ePlane y).2))
      rw [prependCoordinates_pairing, ← heW]
      exact hpair

end

namespace Construction

open OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticCoordinates

/-- The coordinate-existence conclusion of UnitarySplitting, proved from its natural
field and form hypotheses. -/
theorem symplecticFrame_nonempty
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CharZero F] [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
    (m n : ℕ) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (hHermitian : ∀ i j, H j i = σ (H i j))
    (hSkewHermitian : ∀ i j, K j i = -σ (K i j))
    (hHNondegenerate : H.det ≠ 0) (hKNondegenerate : K.det ≠ 0) :
    Nonempty (Oscillator.Construction.SymplecticFrame σ H K) := by
  have hB := TracePairing.Construction.traceTensorBilinear_is_symplectic hQuadratic σ H K
    hHermitian hSkewHermitian hHNondegenerate hKNondegenerate
  obtain ⟨d, e, he⟩ := exists_coordinates (TracePairing.Construction.traceTensorBilinear σ H K) hB.1 hB.2
  have hd : d = m * n := by
    have hdim := e.finrank_eq
    simp [Coordinates, Module.finrank_pi_fintype, hQuadratic] at hdim
    omega
  subst d
  let eSum := LinearEquiv.sumArrowLequivProdArrow (Fin (m * n)) (Fin (m * n)) F F
  refine ⟨⟨e.trans eSum.symm, ?_⟩⟩
  intro x y
  change Oscillator.Construction.standardSymplecticPairing (m * n) (eSum.symm (e x)) (eSum.symm (e y)) =
    TracePairing.Construction.traceTensorBilinear σ H K x y
  rw [he]
  rfl

end Construction

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticCoordinates
