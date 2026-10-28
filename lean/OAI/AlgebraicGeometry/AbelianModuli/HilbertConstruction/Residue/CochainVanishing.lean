import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.UniversalExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesQuotientFree

/-! # Cochain Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.CochainVanishing.LocalSectionLifting

noncomputable section

/-! A residue cohomology bound for a finite free local model remains valid under every additive functor. Vanishing one degree past the bound also makes the last cycle module and its quotient finite free, with a split inclusion. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u v w
variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem finiteFreeCochain_map_exactAt_of_residue_exactAt
    {D : Type v} [Category.{w} D] [Abelian D]
    (F : ModuleCat.{u} R ⥤ D) [F.Additive]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (q : ℕ)
    (hq : (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (ResidueField R)).mapHomologicalComplex
      (.up ℕ)).obj C).ExactAt q) :
    ((F.mapHomologicalComplex (.up ℕ)).obj C).ExactAt q := by
  have : Module.Finite R (C.sc q).X₁ := hfin ((ComplexShape.up ℕ).prev q)
  have : Module.Free R (C.sc q).X₁ := hfree ((ComplexShape.up ℕ).prev q)
  have : Module.Finite R (C.sc q).X₂ := hfin q
  have : Module.Free R (C.sc q).X₂ := hfree q
  have : Module.Finite R (C.sc q).X₃ := hfin ((ComplexShape.up ℕ).next q)
  have : Module.Free R (C.sc q).X₃ := hfree ((ComplexShape.up ℕ).next q)
  exact UniversalExactness.LocalSectionLifting.finiteFreeShortComplex_map_exact_of_residue_exact F (C.sc q) hq

theorem finiteFreeCochain_map_vanish_above_residue_bound
    {D : Type v} [Category.{w} D] [Abelian D]
    (F : ModuleCat.{u} R ⥤ D) [F.Additive]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (g : ℕ)
    (hres : ∀ q, g < q → IsZero
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (ResidueField R)).mapHomologicalComplex (.up ℕ)).obj C).homology q)) :
    ∀ q, g < q → IsZero (((F.mapHomologicalComplex (.up ℕ)).obj C).homology q) := by
  intro q hq
  exact (finiteFreeCochain_map_exactAt_of_residue_exactAt F C hfin hfree q
    ((HomologicalComplex.exactAt_iff_isZero_homology _ q).mpr (hres q hq))).isZero_homology

theorem finiteFreeCochain_last_cycles_split_finite_free
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (g : ℕ)
    (hres : IsZero ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (ResidueField R)).mapHomologicalComplex
      (.up ℕ)).obj C).homology (g + 1))) :
    Module.Finite R (C.d g (g + 1)).hom.ker ∧
      Module.Free R (C.d g (g + 1)).hom.ker ∧
      Module.Finite R (C.X g ⧸ (C.d g (g + 1)).hom.ker) ∧
      Module.Free R (C.X g ⧸ (C.d g (g + 1)).hom.ker) ∧
      ∃ r : C.X g →ₗ[R] (C.d g (g + 1)).hom.ker,
        r.comp (C.d g (g + 1)).hom.ker.subtype = LinearMap.id := by
  let S := C.sc' g (g + 1) (g + 2)
  have : Module.Finite R S.X₁ := hfin g
  have : Module.Free R S.X₁ := hfree g
  have : Module.Finite R S.X₂ := hfin (g + 1)
  have : Module.Free R S.X₂ := hfree (g + 1)
  have : Module.Finite R S.X₃ := hfin (g + 2)
  have : Module.Free R S.X₃ := hfree (g + 2)
  let Cκ := ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (ResidueField R)).mapHomologicalComplex (.up ℕ)).obj C
  have he : Cκ.ExactAt (g + 1) := (Cκ.exactAt_iff_isZero_homology _).mpr hres
  have hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (ResidueField R) S).Exact :=
    (Cκ.exactAt_iff' g (g + 1) (g + 2) (by simp) (by simp)).mp he
  obtain ⟨hfinK, hfreeK⟩ := Local.FirstCyclesFree.LocalSectionLifting.firstCycles_finite_free_of_residue_exact S hS
  obtain ⟨hfinQ, hfreeQ⟩ := Local.FirstCyclesQuotientFree.LocalSectionLifting.firstCycles_quotient_finite_free_of_residue_exact S hS
  exact ⟨hfinK, hfreeK, hfinQ, hfreeQ, Local.FirstCyclesSplitting.LocalSectionLifting.firstCycles_inclusion_split_of_residue_exact S hS⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.CochainVanishing.LocalSectionLifting
