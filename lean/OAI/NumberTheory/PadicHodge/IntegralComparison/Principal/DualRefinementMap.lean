import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulResolutionCoordinates

/-! # Dual Refinement Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DualRefinementMap

noncomputable section

/-! Principal sections retain the literal dual refinement maps before
applying them to a supported class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U) (q : ℕ)
  (N : X.Modules) {K L T : ChainComplex X.Modules ℕ}

abbrev nativeComplex (K : ChainComplex X.Modules ℕ) :
    CochainComplex ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) ℕ :=
  Koszul.Comparison.nativeComplex U hU N K

def nativeMap (a : T ⟶ K) : nativeComplex U hU N K ⟶ nativeComplex U hU N T :=
  ((InternalHomComplex.sectionHom U hU N).mapHomologicalComplex
    (ComplexShape.down ℕ).symm).map
      ((HomologicalComplex.opFunctor X.Modules (.down ℕ)).map a.op)

theorem map (a : T ⟶ K) :
    (PrincipalReference.Concentration.Reference.functor U hU W q).map
        ((Affine.LocalDualInvariance.functor N).map a.op) =
      (Supported.CechHomotopyEquivalence.functor W q).map (nativeMap U hU N a) :=
  congrArg (Supported.CechHomotopyEquivalence.functor W q).map
    (KoszulResolutionCoordinates.dual_map U hU N a)

variable (a : T ⟶ K)
  [IsIso ((PrincipalReference.Concentration.Reference.functor U hU W q).map
    ((Affine.LocalDualInvariance.functor N).map a.op))]

theorem isIso :
    IsIso ((Supported.CechHomotopyEquivalence.functor W q).map (nativeMap U hU N a)) := by
  rw [← DualRefinementMap.map U hU W q N a]
  infer_instance

private theorem refinement_congr {C : Type*} [Category C]
    {P K T : C} {l l' : K ⟶ T} {r r' : P ⟶ T}
    [IsIso l] [IsIso l'] (hl : l = l') (hr : r = r') :
    r ≫ inv l = r' ≫ inv l' := by
  cases hl
  cases hr
  rfl

abbrev refinement (b : T ⟶ L) :=
  letI := isIso U hU W q N a
  refinement_congr (DualRefinementMap.map U hU W q N a) (DualRefinementMap.map U hU W q N b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DualRefinementMap
