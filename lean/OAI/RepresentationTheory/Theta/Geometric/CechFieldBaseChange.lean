import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldExtension
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechAffineBaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Cech Field Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.CechFieldBaseChange

noncomputable section

/-! Field extension preserves the H1 dimension of the actual geometric
Cech complex; the comparison is the existing tensor base-change map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

theorem fieldExtension_homology_finrank {K T : Type u} [Field K] [CommRing T] [Nontrivial T]
    (f : K →+* T) (C : ShortComplex (ModuleCat.{u} K)) :
    Module.finrank T (C.map (ModuleCat.extendScalars f)).homology = Module.finrank K C.homology := by
  let : Algebra K T := f.toAlgebra
  have := AlgebraicGeometry.Quotients.FiniteDescent.FieldExtension.Construction.FieldExtensionExact.preservesHomology f
  have h := (C.mapHomologyIso (ModuleCat.extendScalars f)).toLinearEquiv.finrank_eq
  change Module.finrank T (C.map (ModuleCat.extendScalars f)).homology =
    Module.finrank T (T ⊗[K] C.homology) at h
  rw [Module.finrank_baseChange] at h
  exact h

theorem geometricCech_H1_finrank_field_baseChange
    {X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T] [Nontrivial Γ(T, ⊤)]
    (hS : IsField Γ(S, ⊤)) (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ π g) (M : X.Modules) [M.IsQuasicoherent]
    {I : Type u} [LinearOrder I] [Finite I] (U : I → X.Opens)
    (ha : ∀ (n : ℕ) (i : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I n), IsAffineOpen (∏ᶜ fun k => U (i.1 k))) :
    Module.finrank Γ(T, ⊤) ((AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.target f ρ M U).sc' 0 1 2).homology =
      Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2).homology := by
  let : Field Γ(S, ⊤) := hS.toField
  have := AlgebraicGeometry.Quotients.FiniteDescent.CechAffineBaseChange.Construction.CechBaseChangeMap.isIso_of_affine_intersections f π ρ g hp M U ha
  let k := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(T, ⊤))
    (ComplexShape.up ℕ) 0 1 2).map (AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g hp.w M U)
  have : IsIso k := inferInstance
  have h := (asIso (ShortComplex.homologyMap k)).toLinearEquiv.finrank_eq
  exact h.symm.trans (fieldExtension_homology_finrank g.appTop.hom
    ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2))

end

end OAI.RepresentationTheory.Theta.Geometric.CechFieldBaseChange
