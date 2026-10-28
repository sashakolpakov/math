import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.LocalClosedFiberIsomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.SourceIsomorphismTransport
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Local Closed Fiber Isomorphism -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LocalClosedFiberIsomorphism

noncomputable section

/-! The closed coefficient fiber detects isomorphism of an arbitrary
finite morphism to a noetherian local affine target when its source is coefficient-flat. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R A : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [Algebra R A] [IsLocalHom (algebraMap R A)]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsFinite f]
variable [Flat (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))]

theorem finiteLocal_isIso_of_closedFiber
    (h : IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))))) : IsIso f := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let C : Type u := Γ(X, ⊤)
  let e : Spec (.of C) ≅ X := X.isoSpec.symm
  let φ : A →+* C := (Spec.preimage (e.hom ≫ f)).hom
  let : Algebra A C := φ.toAlgebra
  let : Algebra R C := (φ.comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  have he : Spec.map (CommRingCat.ofHom (algebraMap A C)) = e.hom ≫ f :=
    Spec.map_preimage (e.hom ≫ f)
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
    rw [he]
    infer_instance
  let : Module.Finite A C := (IsFinite.SpecMap_iff _).mp hfin
  have heR : Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    have hc : CommRingCat.ofHom (algebraMap R C) =
        CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom (algebraMap A C) := rfl
    rw [hc, Spec.map_comp, he, Category.assoc]
  have hfR : Flat (Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
    rw [heR]
    infer_instance
  let : Module.Flat R C := Flat.SpecMap_iff.mp hfR
  have hC : IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))) := by
    rw [he, Relative.SourceIsomorphismTransport.relativeMorphismBaseChange_sourceIso_iff]
    exact h
  have hi := Affine.LocalClosedFiberIsomorphism.affineLocal_isIso_of_closedFiber (R := R) (A := A) (C := C) hC
  rw [he, isIso_comp_left_iff] at hi
  exact hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LocalClosedFiberIsomorphism
