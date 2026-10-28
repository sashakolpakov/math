import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MinimalShortComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberFlatCriterion
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Residue Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueExactness.LocalSectionLifting

noncomputable section

/-! Exactness of a finite free short complex over a local ring follows from exactness over its residue field. Minimal reduction and Nakayama prove the assertion. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem finiteFreeShortComplex_exact_of_residue_exact
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).Exact) : S.Exact := by
  obtain ⟨P⟩ := MinimalShortComplex.LocalSectionLifting.exists_localMinimalShortComplex S
  let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)
  let T : ShortComplex (ModuleCat.{u} (IsLocalRing.ResidueField R)) :=
    HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) P.complex
  let eH : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology ≅ T.homology :=
    ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMapHomologyIso F P.equivalence
  have hz : IsZero T.homology := eH.isZero_iff.mp
    ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).exact_iff_isZero_homology.mp hS)
  have hf : T.f = 0 := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_f_zero R (IsLocalRing.ResidueField R)
    P.complex P.incoming_residue_zero
  have hg : T.g = 0 := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_g_zero R (IsLocalRing.ResidueField R)
    P.complex P.outgoing_residue_zero
  let eT : T.homology ≅ T.X₂ := (ShortComplex.LeftHomologyData.ofZeros T hf hg).homologyIso
  have ht : Subsingleton (IsLocalRing.ResidueField R ⊗[R] P.complex.X₂) :=
    ModuleCat.subsingleton_of_isZero (eT.isZero_iff.mp hz)
  have : Subsingleton P.complex.X₂ :=
    (IsLocalRing.subsingleton_tensorProduct (R := R) (M := P.complex.X₂)).mp ht
  have hp : IsZero P.complex.homology :=
    ShortComplex.isZero_homology_of_isZero_X₂ (S := P.complex) (ModuleCat.isZero_of_subsingleton _)
  exact S.exact_iff_isZero_homology.mpr (P.homologyIso.isZero_iff.mpr hp)

theorem finiteFreeCochain_acyclic_of_residue_acyclic
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ n, Module.Finite R (C.X n)) (hfree : ∀ n, Module.Free R (C.X n))
    (hC : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)).mapHomologicalComplex
      (.up ℕ)).obj C).Acyclic) : C.Acyclic := by
  intro n
  have : Module.Finite R (C.sc n).X₁ := hfin ((ComplexShape.up ℕ).prev n)
  have : Module.Free R (C.sc n).X₁ := hfree ((ComplexShape.up ℕ).prev n)
  have : Module.Finite R (C.sc n).X₂ := hfin n
  have : Module.Free R (C.sc n).X₂ := hfree n
  have : Module.Finite R (C.sc n).X₃ := hfin ((ComplexShape.up ℕ).next n)
  have : Module.Free R (C.sc n).X₃ := hfree ((ComplexShape.up ℕ).next n)
  change (C.sc n).Exact
  exact finiteFreeShortComplex_exact_of_residue_exact (C.sc n) (hC n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueExactness.LocalSectionLifting
