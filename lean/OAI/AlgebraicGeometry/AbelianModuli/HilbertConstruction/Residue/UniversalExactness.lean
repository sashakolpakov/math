import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueExactness
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Universal Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.UniversalExactness.LocalSectionLifting

noncomputable section

/-! Residue exactness of a finite free short complex over a local ring implies exactness after every additive functor. Minimal cancellation gives a zero middle term, so no flatness of the functor is needed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem minimal_middle_isZero_of_residue_exact
    {S : ShortComplex (ModuleCat.{u} R)} (P : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S)
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).Exact) :
    IsZero P.complex.X₂ := by
  let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)
  let T := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) P.complex
  let eH : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).homology ≅
      T.homology := ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMapHomologyIso F P.equivalence
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
  exact ModuleCat.isZero_of_subsingleton _

theorem finiteFreeShortComplex_map_exact_of_residue_exact
    {D : Type v} [Category.{w} D] [Abelian D]
    (F : ModuleCat.{u} R ⥤ D) [F.Additive]
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).Exact) :
    (S.map F).Exact := by
  obtain ⟨P⟩ := Local.MinimalShortComplex.LocalSectionLifting.exists_localMinimalShortComplex S
  have hz : IsZero P.complex.X₂ := minimal_middle_isZero_of_residue_exact P hS
  let eH : (S.map F).homology ≅ (P.complex.map F).homology :=
    ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMapHomologyIso F P.equivalence
  have ht : IsZero (P.complex.map F).homology :=
    ShortComplex.isZero_homology_of_isZero_X₂ (S := P.complex.map F) (F.map_isZero hz)
  exact (S.map F).exact_iff_isZero_homology.mpr (eH.isZero_iff.mpr ht)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.UniversalExactness.LocalSectionLifting
