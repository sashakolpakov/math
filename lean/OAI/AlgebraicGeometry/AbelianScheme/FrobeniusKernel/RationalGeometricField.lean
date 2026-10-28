import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RationalResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Rational Geometric Field -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RationalGeometricField.Construction

noncomputable section

/-!
Compare the algebraic closure of the residue field used by CMPoints with
the fixed algebraically closed field of an actual rational point.
The comparison retains the complete factorization into the source
scheme, so it can be used for the original family and all its data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ p = 𝟙 _)

include hx in
theorem rationalResidueField_isAlgClosed : IsAlgClosed (X.residueField (x (IsLocalRing.closedPoint k))) :=
  IsAlgClosed.of_ringEquiv k _ (RationalResidueField.Construction.rationalResidueFieldIso k p x hx).symm.commRingCatIsoToRingEquiv

def rationalResidueClosureIso :
    X.residueField (x (IsLocalRing.closedPoint k)) ≅
      CommRingCat.of (AlgebraicClosure (X.residueField (x (IsLocalRing.closedPoint k)))) := by
  let R := X.residueField (x (IsLocalRing.closedPoint k))
  letI : IsAlgClosed R := rationalResidueField_isAlgClosed k p x hx
  exact (RingEquiv.ofBijective (algebraMap R (AlgebraicClosure R))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).toCommRingCatIso

/-- The CMPoints-style geometric residue field is actually the fixed
algebraically closed field of the given point. -/
def rationalGeometricFieldIso :
    CommRingCat.of (AlgebraicClosure (X.residueField (x (IsLocalRing.closedPoint k)))) ≅ CommRingCat.of k :=
  (rationalResidueClosureIso k p x hx).symm ≪≫ RationalResidueField.Construction.rationalResidueFieldIso k p x hx

theorem rationalGeometricFieldIso_scalar :
    CommRingCat.ofHom (algebraMap (X.residueField (x (IsLocalRing.closedPoint k)))
      (AlgebraicClosure (X.residueField (x (IsLocalRing.closedPoint k))))) ≫
        (rationalGeometricFieldIso k p x hx).hom = (RationalResidueField.Construction.rationalResidueFieldIso k p x hx).hom := by
  change (rationalResidueClosureIso k p x hx).hom ≫
    (rationalResidueClosureIso k p x hx).inv ≫ (RationalResidueField.Construction.rationalResidueFieldIso k p x hx).hom = _
  rw [Iso.hom_inv_id_assoc]

/-- The original geometric point is unchanged after passing through
the algebraic closure of its native residue field. -/
theorem rationalGeometricFieldIso_factor :
    Spec.map (rationalGeometricFieldIso k p x hx).hom ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (x (IsLocalRing.closedPoint k)))
        (AlgebraicClosure (X.residueField (x (IsLocalRing.closedPoint k)))))) ≫
          X.fromSpecResidueField (x (IsLocalRing.closedPoint k))) = x := by
  rw [← Category.assoc, ← Spec.map_comp, rationalGeometricFieldIso_scalar,
    RationalResidueField.Construction.rationalResidueFieldIso_factor]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RationalGeometricField.Construction
