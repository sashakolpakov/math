import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricFlatness
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Affine Fiber Flatness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineFiberFlatness.Construction

noncomputable section

/-! Affine scheme forms of the Openness local flatness criterion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry IsLocalRing TensorProduct
open scoped TensorProduct

universe u

/-- A finite, locally finitely presented affine morphism gives a finitely
presented module on global sections. -/
theorem finitePresentation_module_appTop
    {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y]
    [IsFinite f] [LocallyOfFinitePresentation f] :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := f.finitePresentation_appTop
  exact Module.FinitePresentation.of_finite_of_finitePresentation _ _

/-- Over a local base and local target, a finite morphism of finite
presentation is flat if its source is base-flat and the closed fiber
becomes flat after a faithfully flat extension. -/
theorem flat_SpecMap_of_flat_closedFiber_baseChange
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Algebra A D] [Algebra (A ⊗[R] ResidueField R) D]
    [IsScalarTower A (A ⊗[R] ResidueField R) D]
    [Module.FaithfullyFlat (A ⊗[R] ResidueField R) D]
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    [Flat (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A D)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))))] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have hfin : (algebraMap A B).Finite :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap A B))).mp inferInstance
  have hfp : (algebraMap A B).FinitePresentation :=
    (LocallyOfFinitePresentation.SpecMap_iff
      (CommRingCat.ofHom (algebraMap A B))).mp inferInstance
  have : Module.Finite A B := RingHom.finite_algebraMap.mp hfin
  have : Algebra.FinitePresentation A B := by
    rwa [RingHom.finitePresentation_algebraMap] at hfp
  have : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp
    ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R B))).mp inferInstance)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap D (D ⊗[A] B)))) := by
    rw [← pullbackSpecIso_inv_fst A D B]
    infer_instance
  have : Module.Flat D (D ⊗[A] B) := RingHom.flat_algebraMap_iff.mp
    ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap D (D ⊗[A] B)))).mp
      inferInstance)
  have : Module.Flat A B := GeometricFlatness.Construction.flat_of_faithfullyFlat_closedFiber R A B D
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineFiberFlatness.Construction
