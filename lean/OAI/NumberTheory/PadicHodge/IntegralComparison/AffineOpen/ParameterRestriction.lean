import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DifferentialBasis
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Regular.Flat

/-! # Parameter Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ParameterRestriction

noncomputable section

/-! Literal affine-open restriction preserves the section ideal,
weak regularity, and the differential basis of a parameter tuple. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
  {g : ℕ} (t : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)

def parameters : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V :=
  fun j => X.left.presheaf.map (homOfLE hVU).op (t j)

theorem span (I : X.left.IdealSheafData)
    (ht : Ideal.span (Set.range t) = I.ideal ⟨U,hU⟩) :
    Ideal.span (Set.range (parameters R X U V hVU t)) = I.ideal ⟨V,hV⟩ := by
  rw [← I.map_ideal (U := ⟨V,hV⟩) (V := ⟨U,hU⟩) hVU,
    ← ht, Ideal.map_span, ← Set.range_comp]
  rfl

include hU hV in
theorem regular (ht : RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (List.ofFn t)) :
    RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)
      (List.ofFn (parameters R X U V hVU t)) := by
  let : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X (homOfLE hVU)
  let : Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionEtale R X (homOfLE hVU) hU hV
  change RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)
    (List.ofFn (fun j => algebraMap (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) (t j)))
  simpa only [List.map_ofFn, Function.comp_def] using ht.of_flat (S := IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)

def basis (b : Module.Basis (Fin g) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U⁄R]) :
    Module.Basis (Fin g) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V⁄R] :=
  DifferentialBasis.basis R X (homOfLE hVU) hU hV b

theorem basis_apply (b : Module.Basis (Fin g) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U⁄R])
    (hb : ∀ j, b j = KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (t j)) (j : Fin g) :
    basis R X U V hU hV hVU b j =
      KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) (parameters R X U V hVU t j) :=
  DifferentialBasis.basis_apply R X (homOfLE hVU) hU hV b t hb j

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ParameterRestriction
