import OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceCoverColimit
import OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleAffineIff
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Sequence Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SequenceCover

noncomputable section

/-! A sequence of affine, faithfully flat, weakly étale scheme maps has
an actual affine covering refinement with compatible projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (D : ℕᵒᵖ ⥤ Scheme.{u}) [∀ n, IsAffine (D.obj n)]
  (hf : ∀ i j (h : i ≤ j), Flat (D.map (homOfLE h).op) ∧
    Surjective (D.map (homOfLE h).op))
  (hw : ∀ n, WeaklyEtale (D.map (homOfLE (Nat.zero_le n)).op))

def rings : ℕ ⥤ CommRingCat.{u} := D.rightOp ⋙ Scheme.Γ

def point : Scheme.{u} := Spec (colimit (rings D))

def projection (n : ℕ) : point D ⟶ D.obj (op n) :=
  Spec.map (colimit.ι (rings D) n) ≫ (D.obj (op n)).isoSpec.inv

theorem projection_comp (i j : ℕ) (h : i ≤ j) :
    projection D j ≫ D.map (homOfLE h).op = projection D i := by
  dsimp only [projection]
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp]
  have he := colimit.w (rings D) (homOfLE h)
  exact congrArg (fun f => Spec.map f ≫ (D.obj (op i)).isoSpec.inv) he

include hf in
theorem ring_faithfullyFlat (i j : ℕ) (h : i ≤ j) :
    ((rings D).map (homOfLE h)).hom.FaithfullyFlat := by
  change (D.map (homOfLE h).op).appTop.hom.FaithfullyFlat
  exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp (hf i j h)

include hw in
theorem ring_weaklyEtale (n : ℕ) :
    PeriodInvariants.WeaklyEtaleRingHom.Property ((rings D).map (homOfLE (Nat.zero_le n))).hom := by
  apply (PeriodInvariants.WeaklyEtaleAffineIff.ringHom _ _ _).mp
  change WeaklyEtale (Spec.map (D.map (homOfLE (Nat.zero_le n)).op).appTop)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @WeaklyEtale)
    (arrowIsoSpecΓOfIsAffine (D.map (homOfLE (Nat.zero_le n)).op))).mp (hw n)

include hf hw in
theorem projection_weaklyEtale : WeaklyEtale (projection D 0) := by
  have : WeaklyEtale (Spec.map (colimit.ι (rings D) 0)) :=
    PeriodInvariants.WeaklyEtaleRingHom.specMap _
      (PeriodInvariants.RingSequenceCoverColimit.weaklyEtale (rings D) (ring_faithfullyFlat D hf)
        (ring_weaklyEtale D hw))
  unfold projection
  infer_instance

include hf in
theorem projection_surjective : Surjective (projection D 0) := by
  have : Surjective (Spec.map (colimit.ι (rings D) 0)) :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (PeriodInvariants.RingSequenceCoverColimit.faithfullyFlat (rings D) (ring_faithfullyFlat D hf))).2
  unfold projection
  infer_instance

instance point_affine : IsAffine (point D) := inferInstanceAs (IsAffine (Spec _))

theorem projection_quasiCompact : QuasiCompact (projection D 0) := by infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SequenceCover
