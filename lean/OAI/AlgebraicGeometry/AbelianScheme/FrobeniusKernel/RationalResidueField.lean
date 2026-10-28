import Mathlib.AlgebraicGeometry.ResidueField

/-! # Rational Residue Field -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RationalResidueField.Construction

noncomputable section

/-!
The residue field at a rational point of a scheme over a field is
canonically the original field. This is the field comparison needed
between the CMPoints geometric-fiber conclusions and FrobeniusKernel's fixed
algebraically closed geometric point; no finite-type hypothesis is
required for this comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ p = 𝟙 _)

def rationalResidueFieldMap : X.residueField (x (IsLocalRing.closedPoint k)) ⟶ CommRingCat.of k :=
  X.descResidueField (Scheme.stalkClosedPointTo x)

theorem rationalResidueFieldMap_factor :
    Spec.map (rationalResidueFieldMap k x) ≫
      X.fromSpecResidueField (x (IsLocalRing.closedPoint k)) = x :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X x

include hx in
theorem rationalResidueFieldMap_bijective : Function.Bijective (rationalResidueFieldMap k x) := by
  let a := rationalResidueFieldMap k x
  let b : CommRingCat.of k ⟶ X.residueField (x (IsLocalRing.closedPoint k)) :=
    Spec.preimage (X.fromSpecResidueField (x (IsLocalRing.closedPoint k)) ≫ p)
  have hba : b ≫ a = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc,
      rationalResidueFieldMap_factor, hx, Spec.map_id]
  refine ⟨a.hom.injective, fun t => ⟨b t, ?_⟩⟩
  exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k => f t) hba

/-- The native residue-field isomorphism retains the factorization
of the original geometric point into the source scheme. -/
def rationalResidueFieldIso : X.residueField (x (IsLocalRing.closedPoint k)) ≅ CommRingCat.of k :=
  (RingEquiv.ofBijective (rationalResidueFieldMap k x).hom
    (rationalResidueFieldMap_bijective k p x hx)).toCommRingCatIso

theorem rationalResidueFieldIso_factor :
    Spec.map (rationalResidueFieldIso k p x hx).hom ≫
      X.fromSpecResidueField (x (IsLocalRing.closedPoint k)) = x :=
  rationalResidueFieldMap_factor k x

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RationalResidueField.Construction
