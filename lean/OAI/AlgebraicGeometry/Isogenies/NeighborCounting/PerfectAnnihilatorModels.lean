import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ModelDescent
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.Annihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison

/-! # Perfect Annihilator Models -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PerfectAnnihilatorModels

noncomputable section

/-! Actual perfect finite flat Cartier duality constructs the original
relative annihilator model. This includes integral q-primary kernels;
the target remains the original multiplicative group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ModelDescent OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

universe u

variable {S : Scheme.{u}} (G K : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj K.X]
  [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
  (P : Over S) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) (R : F.Model)
  (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := G.X) (B := K.X) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
  (he : e.toSheafPairing.IsPerfect)

def perfectRelativeAnnihilatorModel : (e.relativeAnnihilator F).Model := by
  let Rp := Classical.choice (AbelianScheme.IsogenyQuotient.Parameter.Annihilator.Construction.relativeParameter_annihilator_from_perfect_pairing G K P F R e he).1
  let Rp' : (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter K P (e.relativeAnnihilator F)).Model :=
    (AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison.Construction.relativeParameter_annihilator_comparison G K P F e).symm ▸ Rp
  exact Parameter.ModelDescent.originalParameterModel K P (e.relativeAnnihilator F) Rp'

variable {A : Over S} [GrpObj A] [IsCommMonObj A]
  (n : ℕ) (p r : A ⟶ A) [IsMonHom p] [IsMonHom r]
  [IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p).hom] [Flat (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p).hom]
  [LocallyOfFinitePresentation (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p).hom]

/-- Discharge the complete-kernel model constructor's CartierDuality clause using
perfection of its actual native block pairing. -/
theorem annihilatorModelInput_of_perfect
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r)
      (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) (he : e.toSheafPairing.IsPerfect) :
    Kernel.Models.AnnihilatorModelInput (P := P) n p r e := by
  intro F hF
  obtain ⟨R⟩ := hF
  exact ⟨perfectRelativeAnnihilatorModel (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p))
    (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r)) P F R e he⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PerfectAnnihilatorModels
