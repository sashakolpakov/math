import OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarExtensionKernel
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.CechKernelRepresentation
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections

/-! # Line Bundle Section Algebra -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleSectionAlgebra

noncomputable section

/-! A single finite-type algebra classifies actual global sections of a
projective flat line-bundle family after every affine base change. The
finite model, scalar comparison, and global-section gluing are all derived. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

def finiteModelSectionAlgebraEquiv
    {X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
    [Module.Finite Γ(S, ⊤) (C.X 0)] [Module.Projective Γ(S, ⊤) (C.X 0)]
    [Module.Finite Γ(S, ⊤) (C.X 1)] [Module.Projective Γ(S, ⊤) (C.X 1)]
    (hφ : ∀ (A : Type u) [AddCommGroup A] [Module Γ(S, ⊤) A],
      QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤) ≃
      (Completion.Finite.CochainKernelAlgebra.Construction.cochainKernelAlgebra (C := C) →ₐ[Γ(S, ⊤)] Γ(T, ⊤)) := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  have := Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ g M U φ hp ha hφ
  exact (Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g hp.w M U hU φ).symm.toEquiv.trans
    ((ScalarExtensionKernel.Construction.scalarExtensionKernelEquiv g.appTop.hom C).trans
      (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv Γ(S, ⊤) (C.X 0) (C.d 0 1).hom Γ(T, ⊤)))

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]

include P in
theorem projectiveLineBundle_exists_sectionAlgebra (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    ∃ B : CommAlgCat.{u} Γ(S, ⊤), Algebra.FiniteType Γ(S, ⊤) B ∧
      ∀ (T : Scheme.{u}) [IsAffine T] (g : T ⟶ S),
      letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
      Nonempty (((Scheme.Modules.pullback (pullback.fst X.hom g)).obj L.sheaf).presheaf.obj (op ⊤) ≃
        (B →ₐ[Γ(S, ⊤)] Γ(T, ⊤))) := by
  obtain ⟨C, φ, _hq, _hb, hf, hp, ht⟩ :=
    Quotients.FiniteDescent.ProjectiveBaseRingModel.Construction.ProjectiveCechComplex.exists_actual_finite_projective X P L
  have := hf 0
  have := hf 1
  have := hp 0
  have := hp 1
  refine ⟨CommAlgCat.of Γ(S, ⊤) (Completion.Finite.CochainKernelAlgebra.Construction.cochainKernelAlgebra (C := C)),
    SymmetricAlgebraFiniteType.Construction.finiteProjectiveKernelAlgebra_finiteType Γ(S, ⊤) (C.X 0) (C.d 0 1).hom, ?_⟩
  intro T _ g
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  exact ⟨finiteModelSectionAlgebraEquiv (pullback.fst X.hom g) X.hom (pullback.snd X.hom g) g
    (IsPullback.of_hasPullback X.hom g) L.sheaf (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P)
    (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers X P)
    (fun q i => Quotients.FiniteDescent.ProjectiveCechFlat.Construction.ProjectiveCechComplex.intersection_affine X P q i.1) φ ht⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleSectionAlgebra
