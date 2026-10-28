import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicHypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Coordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TransverseCoordinateFiber

/-! # Logarithmic Boundary Fiber -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicBoundaryFiber.Construction

noncomputable section

/-! Maximal-contact neighborhoods carry the actual boundary into the coefficient hypersurface. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

/-- The relative logarithmic bound produces a pointed hypersurface
neighborhood with boundary models both on the ambient open and on its
actual coefficient hypersurface. All original equations and labels are
retained in both models. -/
theorem exists_modeled_logarithmic_boundary_fiber
    (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (q : Ideal R) [q.IsPrime]
    (hw : ∀ j, w j ∈ q) (J : Ideal R) (n : ℕ)
    (hJ : J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1))
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J (n + 1) = ⊤) :
    ∃ (z : R) (E : Derivation k R R) (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood E z),
      z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ∧ z ∈ q ∧ E z ∉ q ∧
      E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w ∧
      Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryModel k (Localization.Away f) ι
        (fun j => algebraMap R (Localization.Away f) (w j))) ∧
      Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryModel k
        (Localization.Away f ⧸ Ideal.span {algebraMap R (Localization.Away f) z}) ι
        (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap R (Localization.Away f) z})
          (algebraMap R (Localization.Away f) (w j)))) ∧
      ∃ η : Localization.Away f →+* q.ResidueField,
        ∀ r : R, η (algebraMap R (Localization.Away f) r) = algebraMap R q.ResidueField r := by
  classical
  obtain ⟨z, E, f, d, φ, η, hz, hzq, hEz, hE, hφ, hg, hZ, hW, hη⟩ :=
    LogarithmicHypersurface.Construction.exists_modeled_logarithmic_hypersurface M q hw J n hJ hbound
  let U := Localization.Away f
  let g : R →ₐ[k] U := IsScalarTower.toAlgHom k R U
  let e : M.boundaryIndices ↪ Fin d ⊕ Option M.boundaryIndices :=
    ⟨fun s => Sum.inr (some s), fun _ _ h => Option.some.inj (Sum.inr.inj h)⟩
  let N := M.replaceCoordinates g φ hφ hg e hW
  have hn : ∀ j, N.coordinate j ≠ some (Sum.inr none) :=
    M.replaceCoordinates_unused g φ hφ hg e hW (Sum.inr none) (by
      intro s hs
      have hbad : some s = none := Sum.inr.inj hs
      cases hbad)
  let B := N.transverseCoordinateFiber (Sum.inr none) hn
  have hb : Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryModel k (U ⧸ Ideal.span {algebraMap R U z}) ι
      (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap R U z}) (algebraMap R U (w j)))) := by
    have ht := congrArg (fun t : U => Etale.BoundaryModel.Construction.EtaleBoundaryModel k (U ⧸ Ideal.span {t}) ι
      (fun j => Ideal.Quotient.mk (Ideal.span {t}) (algebraMap R U (w j)))) hZ
    exact ⟨ht ▸ B⟩
  exact ⟨z, E, f, hz, hzq, hEz, hE, ⟨N⟩, hb, η, hη⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LogarithmicBoundaryFiber.Construction
