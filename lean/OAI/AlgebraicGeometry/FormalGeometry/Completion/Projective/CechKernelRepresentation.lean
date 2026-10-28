import OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainKernelAlgebraNaturality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SymmetricAlgebraFiniteType
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveBaseRingModel
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Cech Kernel Representation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.CechKernelRepresentation

noncomputable section

/-! A representing algebra, with natural universal property, for the
actual tensor degree-zero cycles of a projective line bundle. The finite
projective model is derived from projective geometry and flatness. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u
variable {R : Type u} [CommRing R]

structure CochainKernelRepresentation (D : CochainComplex (ModuleCat.{u} R) ℕ) where
  algebra : CommAlgCat.{u} R
  finiteType : Algebra.FiniteType R algebra
  equivalence : ∀ A : CommAlgCat.{u} R,
    ((Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.complex A D).d 0 1).hom.ker ≃ (algebra →ₐ[R] A)
  natural : ∀ (A B : CommAlgCat.{u} R) (h : A ⟶ B)
    (x : ((Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.complex A D).d 0 1).hom.ker),
    equivalence B (CochainKernelAlgebraNaturality.Construction.cochainTensorKernelMap D h.hom.toLinearMap x) = h.hom.comp (equivalence A x)

def cochainKernelRepresentationOfFiniteModel
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)
    [Module.Finite R (C.X 0)] [Module.Projective R (C.X 0)]
    [Module.Finite R (C.X 1)] [Module.Projective R (C.X 1)]
    (hφ : ∀ A : CommAlgCat.{u} R, QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ) 0) :
    CochainKernelRepresentation D where
  algebra := CommAlgCat.of R (Completion.Finite.CochainKernelAlgebra.Construction.cochainKernelAlgebra (C := C))
  finiteType := SymmetricAlgebraFiniteType.Construction.finiteProjectiveKernelAlgebra_finiteType R (C.X 0) (C.d 0 1).hom
  equivalence A := by
    have := hφ A
    exact Completion.Finite.CochainKernelAlgebra.Construction.cochainKernelAlgebraEquiv φ A
  natural A B h x := by
    have := hφ A
    have := hφ B
    exact CochainKernelAlgebraNaturality.Construction.cochainKernelAlgebraEquiv_natural φ h.hom x

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]

def projectiveCechKernelRepresentation (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    CochainKernelRepresentation (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P L.sheaf) := by
  apply Classical.choice
  obtain ⟨C, φ, _hφ, _hb, hf, hp, ht⟩ := Quotients.FiniteDescent.ProjectivePerfectCech.Construction.ProjectiveCechComplex.exists_finite_projective X P L
  have := hf 0
  have := hf 1
  have := hp 0
  have := hp 1
  refine ⟨cochainKernelRepresentationOfFiniteModel φ (fun A => ?_)⟩
  have := ht A
  infer_instance

def projectiveActualCechKernelRepresentation (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    CochainKernelRepresentation (Quotients.FiniteDescent.ProjectiveBaseRingModel.Construction.ProjectiveCechComplex.actualComplex X P L.sheaf) := by
  apply Classical.choice
  obtain ⟨C, φ, _hφ, _hb, hf, hp, ht⟩ := Quotients.FiniteDescent.ProjectiveBaseRingModel.Construction.ProjectiveCechComplex.exists_actual_finite_projective X P L
  have := hf 0
  have := hf 1
  have := hp 0
  have := hp 1
  refine ⟨cochainKernelRepresentationOfFiniteModel φ (fun A => ?_)⟩
  have := ht A
  infer_instance

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.CechKernelRepresentation
