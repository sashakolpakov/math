import OAI.RepresentationTheory.Theta.Geometric.SquareZero.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Reduction -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.Reduction

noncomputable section

/-! Reduction by a square-zero ideal preserves all underlying scheme
points, so a parameter constant after reduction has constant image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem squareZeroIdeal_le_nilradical {R : Type*} [CommRing R]
    (I : Ideal R) (hI : I * I = ⊥) : I ≤ nilradical R := by
  intro x hx
  apply mem_nilradical.mpr
  refine ⟨2, ?_⟩
  have h : x * x ∈ I * I := Ideal.mul_mem_mul hx hx
  rw [hI, Submodule.mem_bot] at h
  exact (pow_two x).trans h

theorem squareZeroIdeal_reduction_surjective {R : Type} [CommRing R]
    (I : Ideal R) (hI : I * I = ⊥) :
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
    (squareZeroIdeal_le_nilradical I hI)).surjective⟩

theorem scheme_range_subset_of_surjective_reduction {T U X Y : Scheme}
    (r : U ⟶ T) [Surjective r] (f : T ⟶ Y) (g : U ⟶ X) (j : X ⟶ Y)
    (h : r ≫ f = g ≫ j) : Set.range f ⊆ Set.range j := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨u, hu⟩ := Surjective.surj (f := r) t
  refine ⟨g u, ?_⟩
  have H := congrArg (fun a : U ⟶ Y => a u) h
  change f (r u) = j (g u) at H
  exact H.symm.trans (congrArg f hu)

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.Reduction
