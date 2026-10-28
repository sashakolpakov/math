import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.LogarithmicCoordinates

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Replace local coordinates while retaining actual boundary equations and their labels. -/

universe u v

variable {k R : Type u} {ι : Type v} [CommRing k] [CommRing R] [Algebra k R]
  {w : ι → R}

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.boundaryCoordinate (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (j : ι) :
    Option M.boundaryIndices :=
  (M.coordinate j).pmap (fun s hs => ⟨s, hs⟩)
    (fun s hs => (M.mem_boundaryIndices s).mpr ⟨j, hs⟩)

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.boundaryCoordinate_map (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (j : ι) :
    (M.boundaryCoordinate j).map Subtype.val = M.coordinate j := by
  cases hc : M.coordinate j <;> simp [Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.boundaryCoordinate, hc]

/-- A replacement étale coordinate system that retains every represented
boundary coordinate gives a model for the original, pulled-back equations. -/
def Etale.BoundaryModel.Construction.EtaleBoundaryModel.replaceCoordinates (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    {S σ : Type u} [CommRing S] [Algebra k S] [Fintype σ] [DecidableEq σ]
    (f : R →ₐ[k] S) (φ : MvPolynomial σ k →+* S) (hφ : φ.Etale)
    (hg : ∀ c : k, φ (MvPolynomial.C c) = algebraMap k S c)
    (e : M.boundaryIndices ↪ σ)
    (he : ∀ s : M.boundaryIndices, φ (MvPolynomial.X (e s)) = f (M.map (MvPolynomial.X s.val))) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k S ι (fun j => f (w j)) where
  indices := σ
  finite := inferInstance
  decidableEq := inferInstance
  map := φ
  etale := hφ
  ground := hg
  coordinate := fun j => (M.boundaryCoordinate j).map e
  distinct i j s hi hj := by
    cases hci : M.boundaryCoordinate i with
    | none => simp only [hci, Option.map_none] at hi; cases hi
    | some t =>
        cases hcj : M.boundaryCoordinate j with
        | none => simp only [hcj, Option.map_none] at hj; cases hj
        | some t' =>
            have hi' : e t = s := by simpa only [hci, Option.map_some, Option.some.injEq] using hi
            have hj' : e t' = s := by simpa only [hcj, Option.map_some, Option.some.injEq] using hj
            have ht : t' = t := e.injective (hj'.trans hi'.symm)
            apply M.distinct i j t.val
            · rw [← M.boundaryCoordinate_map i, hci]
              rfl
            · rw [← M.boundaryCoordinate_map j, hcj, ht]
              rfl
  multiplier := fun j => f (M.multiplier j)
  multiplierUnit j := (M.multiplierUnit j).map f.toRingHom
  equation j := by
    rw [M.equation j, map_mul, ← M.boundaryCoordinate_map j]
    cases hc : M.boundaryCoordinate j with
    | none => simp only [Option.map_none, map_one]
    | some t => simp only [Option.map_some, he]

/-- Any coordinate outside the retained boundary embedding remains
unused by every original boundary label in the replacement model. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.replaceCoordinates_unused (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    {S σ : Type u} [CommRing S] [Algebra k S] [Fintype σ] [DecidableEq σ]
    (f : R →ₐ[k] S) (φ : MvPolynomial σ k →+* S) (hφ : φ.Etale)
    (hg : ∀ c : k, φ (MvPolynomial.C c) = algebraMap k S c)
    (e : M.boundaryIndices ↪ σ)
    (he : ∀ s : M.boundaryIndices, φ (MvPolynomial.X (e s)) = f (M.map (MvPolynomial.X s.val)))
    (h : σ) (hh : ∀ s, e s ≠ h) (j : ι) :
    (M.replaceCoordinates f φ hφ hg e he).coordinate j ≠ some h := by
  change (M.boundaryCoordinate j).map e ≠ some h
  cases hc : M.boundaryCoordinate j with
  | none => simp
  | some t => simpa only [Option.map_some, ne_eq, Option.some.injEq] using hh t

end

end OAI.AlgebraicGeometry.Resolution.Blowups
