import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentLifts
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Component Hopf Lift -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentHopfLift.Components

noncomputable section

/-!
Lift a residue homomorphism from a finite etale Hopf algebra to an arbitrary
finite Hopf algebra. HenselianLifting supplies the algebra map. Its uniqueness in finite
target algebras proves preservation of comultiplication, counit, and
antipode. Thus a component quotient lifts as a group morphism without
requiring the original finite flat group to be etale.
-/

open scoped TensorProduct

universe u

section Residue

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

def residueProjection (A : Type u) [CommRing A] [Algebra R A] : A →ₐ[R] ComponentLifts.Components.ResidueAlgebra R A :=
  Ideal.Quotient.mkₐ R ((IsLocalRing.maximalIdeal R).map (algebraMap R A))

def residueAlgMap (f : A →ₐ[R] B) : ComponentLifts.Components.ResidueAlgebra R A →ₐ[R] ComponentLifts.Components.ResidueAlgebra R B :=
  Ideal.quotientMapₐ _ f (by
    rw [← Ideal.map_le_iff_le_comap]
    change ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).map f.toRingHom ≤ _
    rw [Ideal.map_map]
    have hf : f.toRingHom.comp (algebraMap R A) = algebraMap R B :=
      RingHom.ext f.commutes
    rw [hf])

theorem residueAlgMap_projection (f : A →ₐ[R] B) :
    (residueAlgMap R f).comp (residueProjection R A) = (residueProjection R B).comp f :=
  rfl

def residueTensorSquare (f : A →ₐ[R] ComponentLifts.Components.ResidueAlgebra R B) :
    A ⊗[R] A →ₐ[R] ComponentLifts.Components.ResidueAlgebra R (B ⊗[R] B) :=
  Algebra.TensorProduct.lift
    ((residueAlgMap R (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B)).comp f)
    ((residueAlgMap R (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B)).comp f)
    (fun _ _ => Commute.all _ _)

theorem residueTensorSquare_projection (f : A →ₐ[R] B) :
    residueTensorSquare R ((residueProjection R B).comp f) =
      (residueProjection R (B ⊗[R] B)).comp (Algebra.TensorProduct.map f f) := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  change
    (residueAlgMap R (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B))
        ((residueProjection R B) (f a)) *
      (residueAlgMap R (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B))
        ((residueProjection R B) (f b)) = _
  rw [show (residueAlgMap R (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B))
      ((residueProjection R B) (f a)) =
        (residueProjection R (B ⊗[R] B)) (f a ⊗ₜ[R] 1) from rfl]
  rw [show (residueAlgMap R (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B))
      ((residueProjection R B) (f b)) =
        (residueProjection R (B ⊗[R] B)) (1 ⊗ₜ[R] f b) from rfl]
  rw [← map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

end Residue

variable (R C A : Type u) [CommRing R] [HenselianLocalRing R]
  [CommRing C] [HopfAlgebra R C] [CommRing A] [HopfAlgebra R A]
  [Module.Finite R C] [Module.Finite R A] [Algebra.Etale R C]

/-- The group-law equations for a residue component map, expressed in
residue coordinate algebras. These concern only the specified special map. -/
structure ResidueHopfMap where
  map : C →ₐ[R] ComponentLifts.Components.ResidueAlgebra R A
  counit : (residueAlgMap R (Bialgebra.counitAlgHom R A)).comp map =
    (residueProjection R R).comp (Bialgebra.counitAlgHom R C)
  comul : (residueTensorSquare R map).comp (Bialgebra.comulAlgHom R C) =
    (residueAlgMap R (Bialgebra.comulAlgHom R A)).comp map
  antipode : (residueAlgMap R (HopfAlgebra.antipodeAlgHom R A)).comp map =
    map.comp (HopfAlgebra.antipodeAlgHom R C)

namespace ResidueHopfMap

variable {R C A} (φ : ResidueHopfMap R C A)

def algebraLift : C →ₐ[R] A := (OAI.Algebra.LocalRing.HenselianLifting.Construction.finiteEtale_hom_lift R C A φ.map).choose

theorem algebraLift_reduction : (residueProjection R A).comp φ.algebraLift = φ.map :=
  (OAI.Algebra.LocalRing.HenselianLifting.Construction.finiteEtale_hom_lift R C A φ.map).choose_spec.1

theorem algebraLift_unique (f : C →ₐ[R] A)
    (h : (residueProjection R A).comp f = φ.map) : f = φ.algebraLift :=
  (OAI.Algebra.LocalRing.HenselianLifting.Construction.finiteEtale_hom_lift R C A φ.map).choose_spec.2 f h

theorem algebraLift_counit :
    (Bialgebra.counitAlgHom R A).comp φ.algebraLift = Bialgebra.counitAlgHom R C := by
  apply OAI.Algebra.LocalRing.HenselianLifting.Construction.unramified_hom_ext_of_quotient R C _
    (OAI.Algebra.LocalRing.HenselianLifting.Construction.maximalIdeal_map_le_jacobson R R)
  change (residueProjection R R).comp ((Bialgebra.counitAlgHom R A).comp φ.algebraLift) = _
  rw [← AlgHom.comp_assoc, ← residueAlgMap_projection, AlgHom.comp_assoc,
    φ.algebraLift_reduction]
  exact φ.counit

theorem algebraLift_comul :
    (Algebra.TensorProduct.map φ.algebraLift φ.algebraLift).comp (Bialgebra.comulAlgHom R C) =
      (Bialgebra.comulAlgHom R A).comp φ.algebraLift := by
  apply OAI.Algebra.LocalRing.HenselianLifting.Construction.unramified_hom_ext_of_quotient R C _
    (OAI.Algebra.LocalRing.HenselianLifting.Construction.maximalIdeal_map_le_jacobson R (A ⊗[R] A))
  change (residueProjection R (A ⊗[R] A)).comp
    ((Algebra.TensorProduct.map φ.algebraLift φ.algebraLift).comp (Bialgebra.comulAlgHom R C)) =
    (residueProjection R (A ⊗[R] A)).comp ((Bialgebra.comulAlgHom R A).comp φ.algebraLift)
  rw [← AlgHom.comp_assoc, ← residueTensorSquare_projection, φ.algebraLift_reduction,
    ← AlgHom.comp_assoc, ← residueAlgMap_projection, AlgHom.comp_assoc,
    φ.algebraLift_reduction]
  exact φ.comul

theorem algebraLift_antipode :
    (HopfAlgebra.antipodeAlgHom R A).comp φ.algebraLift =
      φ.algebraLift.comp (HopfAlgebra.antipodeAlgHom R C) := by
  apply OAI.Algebra.LocalRing.HenselianLifting.Construction.unramified_hom_ext_of_quotient R C _
    (OAI.Algebra.LocalRing.HenselianLifting.Construction.maximalIdeal_map_le_jacobson R A)
  change (residueProjection R A).comp ((HopfAlgebra.antipodeAlgHom R A).comp φ.algebraLift) =
    (residueProjection R A).comp (φ.algebraLift.comp (HopfAlgebra.antipodeAlgHom R C))
  rw [← AlgHom.comp_assoc, ← residueAlgMap_projection, AlgHom.comp_assoc,
    φ.algebraLift_reduction, ← AlgHom.comp_assoc, φ.algebraLift_reduction]
  exact φ.antipode

/-- The integral component map, including its group law, is constructed. -/
def bialgebraLift : C →ₐc[R] A :=
  BialgHom.ofAlgHom φ.algebraLift φ.algebraLift_counit φ.algebraLift_comul

open _root_.CategoryTheory _root_.AlgebraicGeometry in
/-- Spectrum turns the constructed Hopf map into the integral group map. -/
def groupSchemeMap :
    (hopfSpec (CommRingCat.of R)).obj (.op (CommHopfAlgCat.of R A)) ⟶
      (hopfSpec (CommRingCat.of R)).obj (.op (CommHopfAlgCat.of R C)) :=
  (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom φ.bialgebraLift).op

open _root_.CategoryTheory _root_.AlgebraicGeometry in
/-- Its restriction to the actual residue coordinate scheme is the
specified special group map, as an equality of scheme morphisms. -/
theorem groupSchemeMap_reduction :
    Spec.map (CommRingCat.ofHom (residueProjection R A).toRingHom) ≫
      φ.groupSchemeMap.hom.hom.left = Spec.map (CommRingCat.ofHom φ.map.toRingHom) := by
  change Spec.map (CommRingCat.ofHom (residueProjection R A).toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.algebraLift.toRingHom) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : C →ₐ[R] ComponentLifts.Components.ResidueAlgebra R A => Spec.map (CommRingCat.ofHom f.toRingHom))
    φ.algebraLift_reduction

end ResidueHopfMap

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentHopfLift.Components
