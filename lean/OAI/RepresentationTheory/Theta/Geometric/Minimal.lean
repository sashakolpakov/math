import OAI.RepresentationTheory.Theta.Geometric.MinimalFieldExtensionRanks
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange
import Mathlib.Algebra.Homology.QuasiIso

/-! # Minimal -/

namespace OAI.RepresentationTheory.Theta.Geometric.Minimal

noncomputable section

/-! The number of original minimal equations equals H1 of the actual
geometric Cech complex after a local map to a field. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y S T : Scheme.{u}} [IsLocalRing Γ(S, ⊤)]
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : f ≫ π = ρ ≫ g) (M : X.Modules)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
    [hmodel : QuasiIsoAt (AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ) 1]
    (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))

include h hmodel in
theorem minimal_middle_finrank_eq_geometric_H1
    (hT : IsField Γ(T, ⊤)) [IsLocalHom g.appTop.hom] :
    Module.finrank Γ(S, ⊤) P.complex.X₂ = Module.finrank Γ(T, ⊤)
      ((AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.target f ρ M U).sc' 0 1 2).homology := by
  let : Field Γ(T, ⊤) := hT.toField
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let ψ := AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ
  let k := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(T, ⊤))
    (ComplexShape.up ℕ) 0 1 2).map ψ
  have : ShortComplex.QuasiIso k := (quasiIsoAt_iff' ψ 0 1 2 (by simp) (by simp)).mp hmodel
  have he := (asIso (ShortComplex.homologyMap k)).toLinearEquiv.finrank_eq
  exact (MinimalFieldExtensionRanks.minimal_middle_finrank_eq_field_cohomology P Γ(T, ⊤)).trans he

end

end OAI.RepresentationTheory.Theta.Geometric.Minimal
