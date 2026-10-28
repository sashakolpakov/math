import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange
import Mathlib.AlgebraicGeometry.Fiber

/-! # Fiber Section -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberSection

noncomputable section

/-! Closedness of the locus where a fiber has a nonzero global section. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.FiberSectionSupport

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)

def locus : Set S := {x | Nontrivial Γ((Scheme.Modules.pullback (π.fiberι x)).obj M, ⊤)}

variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
variable [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
variable [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]

include hU

theorem locus_eq
    (hφ : ∀ x, QuasiIsoAt (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (π.fiberι x) π
      (π.fiberToSpecResidueField x) (S.fromSpecResidueField x) (π.fiber_fac x) M U φ) 0) :
    locus π M = S.toSpecΓ ⁻¹' Module.support Γ(S, ⊤)
      (KernelSupportIs.Construction.KernelSupport.dualCokernel (D.d 0 1).hom) := by
  ext x
  have := hφ x
  have h := ModelSection.Construction.ModelSectionSupport.sections_iff (π.fiberι x) π
    (π.fiberToSpecResidueField x) (S.fromSpecResidueField x) (π.fiber_fac x) M U hU φ
    (IsLocalRing.closedPoint (S.residueField x))
  change Nontrivial Γ((Scheme.Modules.pullback (π.fiberι x)).obj M, ⊤) ↔ _
  have hx : (S.fromSpecResidueField x) (IsLocalRing.closedPoint (S.residueField x)) = x :=
    S.fromSpecResidueField_apply x _
  exact h.trans (iff_of_eq (congrArg (fun z => S.toSpecΓ z ∈ Module.support Γ(S, ⊤)
    (KernelSupportIs.Construction.KernelSupport.dualCokernel (D.d 0 1).hom)) hx))

theorem isClosed_of_model [IsAffine S] [M.IsQuasicoherent] [Finite ι]
    (ha : ∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
    (hφ : ∀ (A : Type u) [AddCommGroup A] [Module Γ(S, ⊤) A],
      QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) : IsClosed (locus π M) := by
  have he := locus_eq π M U hU φ (fun x => by
    have hp : IsPullback (π.fiberι x) (π.fiberToSpecResidueField x) π
        (S.fromSpecResidueField x) := IsPullback.of_hasPullback _ _
    have := CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso (π.fiberι x) π
      (π.fiberToSpecResidueField x) (S.fromSpecResidueField x) M U φ hp ha hφ
    infer_instance)
  rw [he]
  exact (Module.isClosed_support (R := Γ(S, ⊤))
    (M := KernelSupportIs.Construction.KernelSupport.dualCokernel (D.d 0 1).hom)).preimage S.toSpecΓ.continuous

end Construction.FiberSectionSupport

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberSection
