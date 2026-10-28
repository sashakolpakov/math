import OAI.RepresentationTheory.Theta.Geometric.UnramifiedEquationFlatness
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Quotient Jacobian Flatness -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuotientJacobianFlatness

noncomputable section

/-! Apply the local Jacobian criterion to the literal quotient ring and
its spectrum, retaining the actual original defining equations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry KaehlerDifferential

universe u
variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
    [IsLocalRing P] [IsNoetherianRing P] [Algebra.FormallySmooth R P] [Module.Flat R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]

theorem quotient_flat_of_few_equations (I : Ideal P) (hI : I ≠ ⊤)
    [Algebra.FormallyUnramified R (P ⧸ I)] {n : ℕ} (v : Fin n → P)
    (hv : Ideal.span (Set.range v) = I) (hn : n ≤ Module.finrank P Ω[P⁄R]) :
    Module.Flat R (P ⧸ I) := by
  have : Nontrivial (P ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (P ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  let E := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
  have : Algebra.FormallySmooth R E.Ring := inferInstanceAs (Algebra.FormallySmooth R P)
  have : Module.Flat R E.Ring := inferInstanceAs (Module.Flat R P)
  have : IsNoetherianRing E.Ring := inferInstanceAs (IsNoetherianRing P)
  have : Module.Free E.Ring Ω[E.Ring⁄R] := inferInstanceAs (Module.Free P Ω[P⁄R])
  have : Module.Finite E.Ring Ω[E.Ring⁄R] := inferInstanceAs (Module.Finite P Ω[P⁄R])
  apply UnramifiedEquationFlatness.flat_of_unramified_ambient_rank E v
  · change Ideal.span (Set.range v) = RingHom.ker (Ideal.Quotient.mk I)
    rw [Ideal.mk_ker]
    exact hv
  · exact hn

theorem quotientSpec_flat_of_few_equations (I : Ideal P) (hI : I ≠ ⊤)
    [FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap R (P ⧸ I))))]
    {n : ℕ} (v : Fin n → P) (hv : Ideal.span (Set.range v) = I)
    (hn : n ≤ Module.finrank P Ω[P⁄R]) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (P ⧸ I)))) := by
  have hu : (algebraMap R (P ⧸ I)).FormallyUnramified :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)
      (φ := CommRingCat.ofHom (algebraMap R (P ⧸ I)))).mp inferInstance
  have : Algebra.FormallyUnramified R (P ⧸ I) := RingHom.formallyUnramified_algebraMap.mp hu
  have : Module.Flat R (P ⧸ I) := quotient_flat_of_few_equations I hI v hv hn
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr this)

end

end OAI.RepresentationTheory.Theta.Geometric.QuotientJacobianFlatness
