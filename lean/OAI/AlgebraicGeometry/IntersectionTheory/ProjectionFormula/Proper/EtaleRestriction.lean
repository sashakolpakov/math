import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkNeighborhood
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Etale.Field

/-! # Etale Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.EtaleRestriction

noncomputable section

/-! A proper morphism becomes finite etale away from the image of
the complement of any etale source open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem etale_locallyQuasiFinite {X Y : Scheme} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  let : Algebra.Etale Γ(Y, U) Γ(X, V) := f.etale_appLE hU hV e
  change Algebra.QuasiFinite Γ(Y, U) Γ(X, V)
  constructor
  intro P _
  exact Algebra.FormallyUnramified.finite_of_free P.ResidueField (P.Fiber Γ(X, V))

variable {X Y : Scheme} (f : X ⟶ Y) [IsProper f] (U : X.Opens)

def bad : Closeds Y := ⟨f '' (U : Set X)ᶜ, f.isClosedMap _ U.isOpen.isClosed_compl⟩

def good : Y.Opens := ⟨(bad f U : Set Y)ᶜ, (bad f U).isClosed.isOpen_compl⟩

theorem preimage_le : f ⁻¹ᵁ good f U ≤ U := by
  intro x hx
  by_contra hn
  exact hx ⟨x, hn, rfl⟩

theorem etale [Etale (U.ι ≫ f)] : Etale (f ∣_ good f U) := by
  let V := good f U
  have he : (f ⁻¹ᵁ V).ι ≫ f = X.homOfLE (preimage_le f U) ≫ (U.ι ≫ f) := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  let : Etale ((f ⁻¹ᵁ V).ι ≫ f) := by rw [he]; infer_instance
  let : Etale ((f ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  exact Etale.of_comp (f ∣_ V) V.ι

theorem finite [Etale (U.ι ≫ f)] : IsFinite (f ∣_ good f U) := by
  let := etale f U
  let := etale_locallyQuasiFinite (f ∣_ good f U)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.EtaleRestriction
