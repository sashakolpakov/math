import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelTensorInjection
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Point Kernel Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointKernelBaseChange

noncomputable section

/-! Exactness and injectivity of the finite model's kernel sequence on
residue fibers persist at every field-valued point, by its canonical
factorization through the residue field and flat extension of fields. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry IsLocalRing
universe u

theorem fieldPoint_native_kernel_exact_and_mono
    (S : Scheme.{u}) [IsAffine S] (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
    (hD : ∀ x : S, (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
       (.up ℕ)).obj D).ExactAt 1)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ S) :
    ((D.d 0 1).hom.shortComplexKer.map (ModuleCat.extendScalars b.appTop.hom)).Exact ∧
      Mono ((ModuleCat.extendScalars b.appTop.hom).map
        (ModuleCat.ofHom (D.d 0 1).hom.ker.subtype)) := by
  let x := b (closedPoint K)
  let φ : S.residueField x ⟶ .of K := S.descResidueField (Scheme.stalkClosedPointTo b)
  let c := Spec.map φ
  have hc : c ≫ S.fromSpecResidueField x = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S b
  let : Algebra (S.residueField x) K := φ.hom.toAlgebra
  have : Flat c := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (S.residueField x) K))
  have hflat : c.appTop.hom.Flat := HasRingHomProperty.appTop (P := @Flat) c inferInstance
  let F := ModuleCat.extendScalars c.appTop.hom
  have : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  let a := (S.fromSpecResidueField x).appTop.hom
  have he : c.appTop.hom.comp a = b.appTop.hom :=
    congrArg (fun f : Spec (.of K) ⟶ S => f.appTop.hom) hc
  let C := (D.d 0 1).hom.shortComplexKer
  have hC : (C.map (ModuleCat.extendScalars a)).Exact :=
    FiberKernelExactness.fiber_native_kernel_exact_of_degree_one_exact S x D (hD x)
  have hCt : (C.map (ModuleCat.extendScalars (c.appTop.hom.comp a))).Exact :=
    (ShortComplex.exact_iff_of_iso (C.mapNatIso (ModuleCat.extendScalarsComp a c.appTop.hom))).mpr
      (hC.map F)
  let i : ModuleCat.of Γ(S, ⊤) (D.d 0 1).hom.ker ⟶ D.X 0 :=
    ModuleCat.ofHom (D.d 0 1).hom.ker.subtype
  have : Mono ((ModuleCat.extendScalars a).map i) :=
    FiberKernelTensorInjection.fiber_native_kernel_mono_of_degree_one_exact S x D (hD x)
  have hi : Mono ((ModuleCat.extendScalars (c.appTop.hom.comp a)).map i) :=
    (Scalar.Monomorphisms.mono_map_iff_of_functor_iso (ModuleCat.extendScalarsComp a c.appTop.hom) i).mpr
      (inferInstance : Mono (F.map ((ModuleCat.extendScalars a).map i)))
  rw [he] at hCt hi
  exact ⟨hCt, hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointKernelBaseChange
