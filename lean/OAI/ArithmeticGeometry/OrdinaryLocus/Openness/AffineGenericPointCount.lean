import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldPointCount
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFiberAlgebra
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericPointCount
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Affine Generic Point Count -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineGenericPointCount.Construction

noncomputable section

/-! The generic geometric point count of a finite map of affine integral schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem geometricPointCard_spec_generic
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B] [FaithfulSMul R B] [Module.Finite R B] :
    let K := (⊥ : Ideal R).ResidueField
    letI := (GenericFiberAlgebra.Construction.isField_genericFiberAlgebra R B K).toField
    Nat.card (DefinitionsTorsion.geometricPoint (Spec (.of R)) (⊥ : PrimeSpectrum R) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) =
      Field.finSepDegree K (K ⊗[R] B) := by
  let K := (⊥ : Ideal R).ResidueField
  let : Field (K ⊗[R] B) := (GenericFiberAlgebra.Construction.isField_genericFiberAlgebra R B K).toField
  let p : Spec (.of R) := (⊥ : PrimeSpectrum R)
  let C := AlgebraicClosure ((Spec (.of R)).residueField p)
  let e := Scheme.Spec.residueFieldIso (.of R) p
  let : Algebra K C :=
    ((algebraMap ((Spec (.of R)).residueField p) C).comp e.inv.hom).toAlgebra
  let : Algebra R C := ((algebraMap K C).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K C := IsScalarTower.of_algebraMap_eq' rfl
  have ht : Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      (DefinitionsTorsion.geometricPoint (Spec (.of R)) p).hom := by
    change Spec.map ((CommRingCat.ofHom (algebraMap R K) ≫ e.inv) ≫
      CommRingCat.ofHom (algebraMap ((Spec (.of R)).residueField p) C)) = _
    have hinner : Spec.map (CommRingCat.ofHom (algebraMap R K) ≫ e.inv) =
        (Spec (.of R)).fromSpecResidueField p :=
      (Spec.map_comp _ _).trans
        (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p)
    exact (Spec.map_comp _ _).trans (congrArg (fun f =>
      Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of R)).residueField p) C)) ≫ f)
      hinner)
  have he := AffinePointCard.Construction.specPointsEquivAlgHom R B C
  rw [ht] at he
  exact (Nat.card_congr (he.trans (AlgHom.liftEquiv R K B C))).trans
    (Field.finSepDegree_eq_of_isAlgClosed K (K ⊗[R] B) C).symm

/-- Every geometric fiber of a finite flat affine map has at most the
separable degree of its generic fiber. -/
theorem geometricPointCard_spec_le_generic_degree
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B] [FaithfulSMul R B] [Module.Finite R B] [Module.Flat R B]
    [Algebra.FinitePresentation R B] (s : Spec (.of R)) :
    let K := (⊥ : Ideal R).ResidueField
    letI := (GenericFiberAlgebra.Construction.isField_genericFiberAlgebra R B K).toField
    Nat.card (DefinitionsTorsion.geometricPoint (Spec (.of R)) s ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ≤
      Field.finSepDegree K (K ⊗[R] B) := by
  let f : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr (by
    change (algebraMap R B).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat f := Flat.SpecMap_iff.mpr (by
    change (algebraMap R B).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr (by
      change (algebraMap R B).FinitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have h := @GenericPointCount.Construction.geometricPointCard_le_generic (Spec (.of R)) inferInstance
    (Over.mk f) ‹IsFinite f› ‹Flat f› ‹LocallyOfFinitePresentation f› s
  rw [genericPoint_eq_bot_of_affine] at h
  exact h.trans_eq (geometricPointCard_spec_generic R B)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineGenericPointCount.Construction
