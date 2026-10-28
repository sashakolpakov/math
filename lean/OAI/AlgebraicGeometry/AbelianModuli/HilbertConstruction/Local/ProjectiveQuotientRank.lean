import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientRetraction
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.LocalRing.Module

/-! # Projective Quotient Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveQuotientRank

noncomputable section

/-! A projective quotient of a finite projective module over a local
ring has additive finite rank. The proof uses a genuine splitting,
and applies to nonreduced local rings. -/
universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

theorem localProjectiveQuotient_finrank_add (P : Submodule R M)
    [Module.Projective R (M ⧸ P)] :
    Module.finrank R (M ⧸ P) + Module.finrank R P = Module.finrank R M := by
  obtain ⟨r, hr⟩ := HilbertScheme.Presentations.Projective.QuotientRetraction.exists_projective_quotient_retraction P
  have hsurj : Function.Surjective r := fun x => ⟨x.val, LinearMap.congr_fun hr x⟩
  have : Module.Finite R P := Module.Finite.of_surjective r hsurj
  have : Module.Projective R P := Module.Projective.of_split P.subtype r hr
  have : Module.Free R P := Module.free_of_flat_of_isLocalRing
  have : Module.Free R (M ⧸ P) := Module.free_of_flat_of_isLocalRing
  have hcompl : IsCompl P r.ker := LinearMap.isCompl_of_proj (fun x => LinearMap.congr_fun hr x)
  let e := P.quotientEquivOfIsCompl r.ker hcompl
  have : Module.Finite R r.ker := Module.Finite.equiv e
  have : Module.Free R r.ker := Module.Free.of_equiv e
  have h := (P.prodEquivOfIsCompl r.ker hcompl).finrank_eq
  rw [Module.finrank_prod, ← e.finrank_eq] at h
  exact (Nat.add_comm _ _).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveQuotientRank
