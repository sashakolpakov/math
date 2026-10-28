import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm
import OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields

/-! # Function Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FunctionFields

noncomputable section

/-! The affine norm formula uses the actual generic-stalk pullback on the
function fields of the schemes. This verifies the canonical fraction-field
comparisons on scalars and then on every rational function. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

universe u

variable (R S : Type u) [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]

local instance (A : Type u) [CommRing A] [IsDomain A] :
    Algebra A (Spec (.of A)).functionField :=
  (StructureSheaf.toStalk A (genericPoint (Spec (.of A)))).hom.toAlgebra

theorem affineMap_genericPoint :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) (genericPoint (Spec (.of S))) =
      genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).mp
    (FaithfulSMul.algebraMap_injective R S)

def affineFieldMap : (Spec (.of R)).functionField ⟶ (Spec (.of S)).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (affineMap_genericPoint R S)

theorem affineFieldMap_toStalk :
    StructureSheaf.toStalk R (genericPoint (Spec (.of R))) ≫ affineFieldMap R S =
      CommRingCat.ofHom (algebraMap R S) ≫
        StructureSheaf.toStalk S (genericPoint (Spec (.of S))) := by
  change (Scheme.ΓSpecIso (.of R)).inv ≫
    (Spec (.of R)).presheaf.germ ⊤ _ (by trivial) ≫ affineFieldMap R S =
      CommRingCat.ofHom (algebraMap R S) ≫ (Scheme.ΓSpecIso (.of S)).inv ≫
        (Spec (.of S)).presheaf.germ ⊤ _ (by trivial)
  rw [affineFieldMap, Cycles.Functoriality.FunctionFields.Construction.genericFieldMap_germ,
    Scheme.ΓSpecIso_inv_naturality_assoc]

attribute [local instance] FractionRing.liftAlgebra

theorem affineFieldMap_square :
    (affineFieldMap R S).hom.comp (Order.affineFunctionFieldIso R).toRingHom =
      (Order.affineFunctionFieldIso S).toRingHom.comp
        (algebraMap (FractionRing R) (FractionRing S)) := by
  apply IsFractionRing.ringHom_ext (A := R)
  intro r
  change affineFieldMap R S (Order.affineFunctionFieldIso R (algebraMap R (FractionRing R) r)) =
    Order.affineFunctionFieldIso S (algebraMap (FractionRing R) (FractionRing S)
      (algebraMap R (FractionRing R) r))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R S (FractionRing S), AlgEquiv.commutes]
  exact congrArg (fun h : CommRingCat.of R ⟶ (Spec (.of S)).functionField => h r)
    (affineFieldMap_toStalk R S)

/-- The norm transported through canonical fraction fields is the native
norm for the actual generic-stalk field map. -/
theorem affineFieldMap_norm (f : FractionRing S) :
    letI := (affineFieldMap R S).hom.toAlgebra
    Order.affineFunctionFieldIso R (Algebra.norm (FractionRing R) f) =
      Algebra.norm (Spec (.of R)).functionField (Order.affineFunctionFieldIso S f) := by
  let := (affineFieldMap R S).hom.toAlgebra
  have h := Algebra.norm_eq_of_equiv_equiv (Order.affineFunctionFieldIso R).toRingEquiv
    (Order.affineFunctionFieldIso S).toRingEquiv (affineFieldMap_square R S) f
  exact (RingEquiv.eq_symm_apply (Order.affineFunctionFieldIso R).toRingEquiv).mp h

/-- The finite affine norm-divisor identity entirely in the schemes' own
function fields and native pushforward. -/
theorem principalDivisor_native_norm [IsDiscreteValuationRing R] [Module.Finite R S]
    [PerfectField (FractionRing R)] (f : (Spec (.of S)).functionField) (hf : f ≠ 0) :
    letI := (affineFieldMap R S).hom.toAlgebra
    CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (DivisorNorm.rationalPrincipalDivisor (Spec (.of S)) f) =
        DivisorNorm.rationalPrincipalDivisor (Spec (.of R))
          (Algebra.norm (Spec (.of R)).functionField f) := by
  let := (affineFieldMap R S).hom.toAlgebra
  obtain ⟨g, rfl⟩ := (Order.affineFunctionFieldIso S).surjective f
  have hg : g ≠ 0 := fun h => hf (by rw [h, map_zero])
  rw [DivisorNorm.principalDivisor_norm S R g hg, affineFieldMap_norm]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FunctionFields
