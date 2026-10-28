import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveBaseRingModel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

/-! # Cech Cover Homology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoverHomology

noncomputable section

/-! Projective cohomology finiteness is independent of the chosen affine cover. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechCoverFiniteness

variable {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
variable (M : X.Modules) [M.IsQuasicoherent]
variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
variable (U : ι → X.Opens) (V : κ → X.Opens)
variable (hU : iSup U = ⊤) (hV : iSup V = ⊤)
variable (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))

def homologyEquiv (q : ℕ) :
    (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology q ≃ₗ[Γ(S, ⊤)]
      (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M V).homology q :=
  (SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv π M U
      hU haU q).trans
    (SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv π M V
      hV haV q).symm

include hU hV haU haV in
theorem finite (q : ℕ) [Module.Finite Γ(S, ⊤) ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homology q)] :
    Module.Finite Γ(S, ⊤) ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M V).homology q) :=
  Module.Finite.equiv (homologyEquiv π M U V hU hV haU haV q)

include hV haV in
theorem projective [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (q : ℕ) :
    Module.Finite Γ(S, ⊤) ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf V).homology q) := by
  have : L.sheaf.IsQuasicoherent := LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : Module.Finite Γ(S, ⊤) ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf
      (ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk π) P)).homology q) :=
    ProjectiveBaseRingModel.Construction.ProjectiveCechComplex.actual_finite (Over.mk π) P L q
  exact finite π L.sheaf (ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk π) P) V
    (ProjectiveCechAt.Construction.ProjectiveCechComplex.covers (Over.mk π) P) hV
    (ProjectiveCechAt.Construction.ProjectiveCechComplex.affine (Over.mk π) P) haV q

end Construction.CechCoverFiniteness

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoverHomology
