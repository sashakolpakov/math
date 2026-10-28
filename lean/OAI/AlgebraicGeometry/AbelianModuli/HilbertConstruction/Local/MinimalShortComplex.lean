import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.IncomingReduction

/-! # Minimal Short Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MinimalShortComplex.LocalSectionLifting

noncomputable section

/-! Minimal forms of finite free short complexes over a local ring. -/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A finite free short complex with both residue-field differentials zero,
homotopy equivalent to the supplied complex. -/
structure LocalMinimalShortComplex (S : ShortComplex (ModuleCat.{u} R)) where
  complex : ShortComplex (ModuleCat.{u} R)
  [firstFinite : Module.Finite R complex.X₁]
  [firstFree : Module.Free R complex.X₁]
  [middleFinite : Module.Finite R complex.X₂]
  [middleFree : Module.Free R complex.X₂]
  [lastFinite : Module.Finite R complex.X₃]
  [lastFree : Module.Free R complex.X₃]
  equivalence : ShortComplex.HomotopyEquiv S complex
  hom_h₀ : equivalence.homotopyHomInvId.h₀ = 0
  inv_h₀ : equivalence.homotopyInvHomId.h₀ = 0
  incoming_residue_zero : complex.f.hom.baseChange (IsLocalRing.ResidueField R) = 0
  outgoing_residue_zero : complex.g.hom.baseChange (IsLocalRing.ResidueField R) = 0

attribute [instance] LocalMinimalShortComplex.firstFinite LocalMinimalShortComplex.firstFree
  LocalMinimalShortComplex.middleFinite LocalMinimalShortComplex.middleFree
  LocalMinimalShortComplex.lastFinite LocalMinimalShortComplex.lastFree

theorem exists_localMinimalShortComplex (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃] :
    Nonempty (LocalMinimalShortComplex S) := by
  obtain ⟨P⟩ := DifferentialNormalForm.LocalSectionLifting.exists_localMinimalDifferential S.X₂ S.X₃ S.g.hom
  let T := OutgoingReduction.LocalSectionLifting.localOutgoingReducedComplex S P
  have hT₁F : Module.Finite R T.X₁ := ‹Module.Finite R S.X₁›
  have hT₁Free : Module.Free R T.X₁ := ‹Module.Free R S.X₁›
  have hT₂F : Module.Finite R T.X₂ := P.sourceFinite
  have hT₂Free : Module.Free R T.X₂ := P.sourceFree
  obtain ⟨Q⟩ := DifferentialNormalForm.LocalSectionLifting.exists_localMinimalDifferential T.X₁ T.X₂ T.f.hom
  exact ⟨{
    complex := IncomingReduction.LocalSectionLifting.localIncomingReducedComplex T Q
    firstFinite := Q.sourceFinite
    firstFree := Q.sourceFree
    middleFinite := Q.targetFinite
    middleFree := Q.targetFree
    lastFinite := P.targetFinite
    lastFree := P.targetFree
    equivalence := (OutgoingReduction.LocalSectionLifting.localOutgoingReduction S P).trans (IncomingReduction.LocalSectionLifting.localIncomingReduction T Q)
    hom_h₀ := ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquiv_trans_hom_h₀ _ _
      (OutgoingReduction.LocalSectionLifting.localOutgoingReduction_hom_h₀ S P) (IncomingReduction.LocalSectionLifting.localIncomingReduction_hom_h₀ T Q)
    inv_h₀ := ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquiv_trans_inv_h₀ _ _
      (OutgoingReduction.LocalSectionLifting.localOutgoingReduction_inv_h₀ S P) (IncomingReduction.LocalSectionLifting.localIncomingReduction_inv_h₀ T Q)
    incoming_residue_zero := IncomingReduction.LocalSectionLifting.localIncomingReduced_residue_zero T Q
    outgoing_residue_zero := IncomingReduction.LocalSectionLifting.localIncomingReduced_preserves_outgoing_residue_zero T Q
      (OutgoingReduction.LocalSectionLifting.localOutgoingReduced_residue_zero S P) }⟩

def LocalMinimalShortComplex.homologyIso {S : ShortComplex (ModuleCat.{u} R)}
    (P : LocalMinimalShortComplex S) : S.homology ≅ P.complex.homology :=
  ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivHomologyIso P.equivalence

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MinimalShortComplex.LocalSectionLifting
