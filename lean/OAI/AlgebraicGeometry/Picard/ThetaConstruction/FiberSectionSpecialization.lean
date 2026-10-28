import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicCohomologyScalarBridge
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint

/-! # Fiber Section Specialization -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.FiberSectionSpecialization.Geometric

noncomputable section

/-! The vanishing of actual fiber sections is open for an original
proper flat line family. The finite cohomology model is constructed,
so nonzero fiber sections persist under specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

private theorem cochainScalar_zero_iff {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) [Module.Finite R (C.X 0)]
    {N : ModuleCat.{u} K}
    (e : (AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel.cochainScalarExtension C K).homology 0 ≃ₗ[K] N) :
    Module.finrank K ((AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel.cochainScalarExtension C K).homology 0) = 0 ↔ Subsingleton N := by
  let : Module.Finite K ((C.d 0 1).hom.baseChange K).ker := inferInstance
  let : Module.Finite K ((AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel.cochainScalarExtension C K).homology 0) :=
    Module.Finite.equiv (AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel.cochainScalarExtensionZeroKernelEquiv C K).symm
  exact Module.finrank_zero_iff.trans e.toEquiv.subsingleton_congr

private theorem nativeFiberSection_subsingleton {X S : Scheme.{u}}
    (f : X ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ) (x : S)
    (e : Nonempty
      ((((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
        (.up ℕ)).obj C).homology 0 ≅
          (AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.fiberToSpecResidueField x).appTop.hom 0).obj
            (L.pullback (f.fiberι x)).sheaf)) :
    Subsingleton ((((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj C).homology 0) ↔ Subsingleton Γ((L.pullback (f.fiberι x)).sheaf, ⊤) :=
  (Classical.choice e).toLinearEquiv.toEquiv.subsingleton_congr.trans
    (AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
      (f.fiberToSpecResidueField x).appTop.hom (L.pullback (f.fiberι x)).sheaf).toEquiv.subsingleton_congr

private theorem nativeCochainZeroOpen_mem {S : Scheme.{u}}
    (C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
    [Module.Finite Γ(S, ⊤) (C.X 0)] [Module.Projective Γ(S, ⊤) (C.X 0)]
    [Module.Finite Γ(S, ⊤) (C.X 1)] [Module.Projective Γ(S, ⊤) (C.X 1)] (x : S) :
    x ∈ AbelianModuli.HilbertConstruction.Cochain.ZeroDimensionOpen.cochainZeroDimensionOpen C 0 ↔
      Subsingleton ((((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
        (.up ℕ)).obj C).homology 0) := by
  let V := AbelianModuli.HilbertConstruction.Cochain.ZeroDimensionOpen.cochainZeroDimensionOpen C 0
  let b : Spec (S.residueField x) ⟶ S := S.fromSpecResidueField x
  let : Field Γ(Spec (S.residueField x), ⊤) := Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField _
  let : Algebra Γ(S, ⊤) Γ(Spec (S.residueField x), ⊤) := b.appTop.hom.toAlgebra
  have hr : Set.range b ⊆ (V : Set S) ↔ x ∈ V := by
    constructor
    · intro h
      have ht : b (default : Spec (S.residueField x)) ∈ V :=
        h ⟨(default : Spec (S.residueField x)), rfl⟩
      exact (congrArg (fun y : S => y ∈ V)
        (Scheme.fromSpecResidueField_apply x default)).mp ht
    · intro h y hy
      obtain ⟨z, rfl⟩ := hy
      change b z ∈ V
      exact (congrArg (fun y : S => y ∈ V)
        (Scheme.fromSpecResidueField_apply x z)).mpr h
  have ho := AbelianModuli.HilbertConstruction.Cochain.ZeroDimensionOpen.cochainZeroDimensionOpen_field_point (S := S) C (K := S.residueField x) b 0
  simp only [Nat.le_zero] at ho
  exact hr.symm.trans (ho.trans (cochainScalar_zero_iff
    (K := Γ(Spec (S.residueField x), ⊤)) C (IntrinsicCohomologyScalarBridge.Geometric.nativeCochainScalarHomologyEquiv b.appTop.hom C 0).symm))

private theorem fiberSectionZeroOpen_from_model {X S : Scheme.{u}}
    (f : X ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
    [Module.Finite Γ(S, ⊤) (C.X 0)] [Module.Projective Γ(S, ⊤) (C.X 0)]
    [Module.Finite Γ(S, ⊤) (C.X 1)] [Module.Projective Γ(S, ⊤) (C.X 1)]
    (hfiber : ∀ x : S, Nonempty
      ((((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
        (.up ℕ)).obj C).homology 0 ≅
          (AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.fiberToSpecResidueField x).appTop.hom 0).obj
            (L.pullback (f.fiberι x)).sheaf)) :
    ∃ V : S.Opens, ∀ x : S, x ∈ V ↔ Subsingleton Γ((L.pullback (f.fiberι x)).sheaf, ⊤) :=
  ⟨AbelianModuli.HilbertConstruction.Cochain.ZeroDimensionOpen.cochainZeroDimensionOpen C 0, fun x =>
    (nativeCochainZeroOpen_mem C x).trans (nativeFiberSection_subsingleton f L C x (hfiber x))⟩

variable {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)

theorem exists_fiberSectionZeroOpen : ∃ V : S.Opens, ∀ x : S,
    x ∈ V ↔ Subsingleton Γ((L.pullback (f.fiberι x)).sheaf, ⊤) := by
  obtain ⟨C, _hb, hf, hp, _hc, hfiber⟩ := AbelianModuli.HilbertConstruction.ProperFlat.FiberwiseCohomologyModel.properFlat_exists_fiberwise_cohomology_model f L
  let : Module.Finite Γ(S, ⊤) (C.X 0) := hf 0
  let : Module.Projective Γ(S, ⊤) (C.X 0) := hp 0
  let : Module.Finite Γ(S, ⊤) (C.X 1) := hf 1
  let : Module.Projective Γ(S, ⊤) (C.X 1) := hp 1
  exact fiberSectionZeroOpen_from_model f L C (fun x => hfiber x 0)

theorem fiberSections_nontrivial_specializes {x y : S} (hxy : x ⤳ y)
    (hx : Nontrivial Γ((L.pullback (f.fiberι x)).sheaf, ⊤)) :
    Nontrivial Γ((L.pullback (f.fiberι y)).sheaf, ⊤) := by
  obtain ⟨V, hV⟩ := exists_fiberSectionZeroOpen f L
  by_contra hy
  have hym := (hV y).mpr (not_nontrivial_iff_subsingleton.mp hy)
  have hxm := hxy.mem_open V.isOpen hym
  exact (not_subsingleton_iff_nontrivial.mpr hx) ((hV x).mp hxm)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.FiberSectionSpecialization.Geometric
